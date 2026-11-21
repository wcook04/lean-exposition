import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Phi
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.PhiBound

open Breakdown.Freq

theorem rpow_le_one_add {s g : ℝ} (hs : 0 ≤ s) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) : s ^ g ≤ 1 + s := by
  rcases le_total s 1 with h | h
  · have := Real.rpow_le_one hs h hg0
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hg1
    rw [Real.rpow_one] at this
    linarith

theorem rpow_mul_exp_neg_le_one {s g : ℝ} (hs : 0 ≤ s) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    s ^ g * Real.exp (-s) ≤ 1 := by
  have h1 := rpow_le_one_add hs hg0 hg1
  have h2 := Real.add_one_le_exp s
  calc s ^ g * Real.exp (-s) ≤ Real.exp s * Real.exp (-s) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem rpow_mul_exp_le {y τ g : ℝ} (hy : 0 ≤ y) (hτ : 0 < τ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    y ^ g * Real.exp (-(τ * y)) ≤ τ ^ (-g) := by
  have h := rpow_mul_exp_neg_le_one (mul_nonneg hτ.le hy) hg0 hg1
  rw [Real.mul_rpow hτ.le hy] at h
  have hp : 0 < τ ^ g := Real.rpow_pos_of_pos hτ g
  rw [Real.rpow_neg hτ.le]
  calc y ^ g * Real.exp (-(τ * y)) = (τ ^ g)⁻¹ * (τ ^ g * y ^ g * Real.exp (-(τ * y))) := by
        rw [mul_assoc (τ ^ g), ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    _ ≤ (τ ^ g)⁻¹ * 1 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
    _ = (τ ^ g)⁻¹ := mul_one _

theorem continuous_rpowNorm {α : ℝ} (hα : 0 ≤ α) :
    Continuous (fun ξ : Space => (2 * π * ‖ξ‖) ^ (2 * α)) :=
  (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr (by linarith))

theorem fracPhiFactor_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ fracPhiFactor α τ ξ := by
  unfold fracPhiFactor
  positivity

theorem fracPhiFactor_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    |fracPhiFactor α τ ξ| ≤ τ ^ (-(1 / (2 * α))) := by
  have hr : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  have h2 : (2 * α) ≠ 0 := (by linarith : (0 : ℝ) < 2 * α).ne'
  have e : fracPhiFactor α τ ξ = ((2 * π * ‖ξ‖) ^ (2 * α)) ^ (1 / (2 * α)) *
      Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) := by
    unfold fracPhiFactor
    rw [← Real.rpow_mul hr, mul_one_div_cancel h2, Real.rpow_one]
  rw [abs_of_nonneg (fracPhiFactor_nonneg α τ ξ), e]
  apply rpow_mul_exp_le (Real.rpow_nonneg hr _) hτ (div_nonneg zero_le_one (by linarith))
  rw [div_le_one (by linarith)]
  linarith

theorem sqFracHeat_nonneg (α τ : ℝ) (ξ : Space) : 0 ≤ sspFactor ξ * fracHeatFactor α τ ξ := by
  unfold sspFactor fracHeatFactor
  positivity

theorem sqFracHeat_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    |sspFactor ξ * fracHeatFactor α τ ξ| ≤ τ ^ (-(1 / α)) := by
  have hr : 0 ≤ 2 * π * ‖ξ‖ := by positivity
  have ha : α ≠ 0 := (by linarith : (0 : ℝ) < α).ne'
  have e2 : 2 * α * (1 / α) = (2 : ℝ) := by field_simp
  have e : sspFactor ξ * fracHeatFactor α τ ξ = ((2 * π * ‖ξ‖) ^ (2 * α)) ^ (1 / α) *
      Real.exp (-(τ * (2 * π * ‖ξ‖) ^ (2 * α))) := by
    unfold sspFactor fracHeatFactor
    rw [max_eq_left hτ.le, ← Real.rpow_mul hr, e2, Real.rpow_two]
    ring
  rw [abs_of_nonneg (sqFracHeat_nonneg α τ ξ), e]
  apply rpow_mul_exp_le (Real.rpow_nonneg hr _) hτ (div_nonneg zero_le_one (by linarith))
  rw [div_le_one (by linarith)]
  linarith

theorem fracHeatFactor_le (α τ : ℝ) (ξ : Space) : |fracHeatFactor α τ ξ| ≤ 1 := by
  unfold fracHeatFactor
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ max τ 0 * (2 * π * ‖ξ‖) ^ (2 * α) := by positivity
  linarith

theorem continuous_fracPhiFactor {α : ℝ} (hα : 0 ≤ α) (τ : ℝ) : Continuous (fracPhiFactor α τ) := by
  unfold fracPhiFactor
  exact (continuous_const.mul continuous_norm).mul
    (Real.continuous_exp.comp ((continuous_const.mul (continuous_rpowNorm hα)).neg))

theorem continuous_fracHeatFactor {α : ℝ} (hα : 0 ≤ α) (τ : ℝ) :
    Continuous (fracHeatFactor α τ) := by
  unfold fracHeatFactor
  exact Real.continuous_exp.comp ((continuous_const.mul (continuous_rpowNorm hα)).neg)

theorem continuous_sqFracHeat {α : ℝ} (hα : 0 ≤ α) (τ : ℝ) :
    Continuous (fun ξ => sspFactor ξ * fracHeatFactor α τ ξ) := by
  have h := continuous_fracHeatFactor hα τ
  unfold sspFactor
  exact (continuous_const.mul (continuous_norm.pow 2)).mul h

end Breakdown.FracInternal.PhiBound

namespace Breakdown.Freq

open Breakdown.FracInternal.PhiBound Internal.Phi in
theorem fracPhiBoundsVelocity (α : ℝ) (hα : 1 < α) (h1 : FracHeatSemigroup α) :
    FracPhiBounds α ∧ FracPhiVelocity α := by
  have h0 : (0 : ℝ) ≤ α := by linarith
  have hF := fieldOpRealized_holds
  have hheat : ∀ τ (ψ : X), ((fracHeatX α τ ψ : X) : L2C) =ᵐ[volume]
      fun ξ => fracHeatFactor α τ ξ • (ψ : L2C) ξ := by
    intro τ ψ
    rw [h1.2.2.2.2.2 τ ψ]
    exact scalarOp_ae hF (continuous_fracHeatFactor h0 τ) (fracHeatFactor_le α τ) (ψ : L2C)
  have hvel : FracPhiVelocity α := by
    intro τ hτ ψ h hssp
    have hgmem := scalarOp_mem hF (continuous_fracPhiFactor h0 τ) (fracPhiFactor_le hα hτ)
      (fun ξ => by simp [fracPhiFactor]) ψ.2
    have hg : IsHalfSspOf ⟨_, hgmem⟩ h := by
      unfold IsHalfSspOf
      filter_upwards [hssp, hheat τ ψ,
        scalarOp_ae hF (continuous_fracPhiFactor h0 τ) (fracPhiFactor_le hα hτ) (ψ : L2C)]
        with ξ e1 e2 e3
      rw [e1, e2, e3, smul_smul, smul_smul]
      congr 1
      unfold sspFactor fracHeatFactor fracPhiFactor
      rw [max_eq_left hτ.le]
      ring
    exact (velocityInverts_holds _ h hg).symm
  refine ⟨⟨‖toPhys‖ + ‖velocity‖ + 1, fun τ hτ ψ => ?_⟩, hvel⟩
  have hmem := scalarOp_mem hF (continuous_sqFracHeat h0 τ) (sqFracHeat_le hα hτ)
    (fun ξ => by simp [sspFactor, fracHeatFactor]) ψ.2
  have hssp : IsSspOf (fracHeatX α τ ψ) ⟨_, hmem⟩ := by
    unfold IsSspOf
    filter_upwards [hheat τ ψ,
      scalarOp_ae hF (continuous_sqFracHeat h0 τ) (sqFracHeat_le hα hτ) (ψ : L2C)] with ξ e1 e2
    rw [e2, e1, smul_smul]
  have hae := hvel τ hτ ψ _ hssp
  have hXn := scalarOp_norm_le hF (continuous_sqFracHeat h0 τ) (sqFracHeat_le hα hτ) (ψ : L2C)
  have hPn := scalarOp_norm_le hF (continuous_fracPhiFactor h0 τ) (fracPhiFactor_le hα hτ)
    (ψ : L2C)
  have hψ : 0 ≤ ‖ψ‖ := norm_nonneg _
  have hk : 0 ≤ τ ^ (-(1 / (2 * α))) := Real.rpow_nonneg hτ.le _
  have hi : 0 ≤ τ ^ (-(1 / α)) := Real.rpow_nonneg hτ.le _
  have hT : 0 ≤ ‖toPhys‖ := norm_nonneg _
  have hV : 0 ≤ ‖velocity‖ := norm_nonneg _
  refine ⟨(Lp.memLp _).ae_eq hae.symm, ?_, ?_⟩
  · rw [← Lp.norm_def]
    have e : fracPhiX α τ ψ = toPhys (fieldOp id
      (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C)) := rfl
    rw [e]
    calc ‖toPhys (fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
          (ψ : L2C))‖
        ≤ ‖toPhys‖ * ‖fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
          (ψ : L2C)‖ := toPhys.le_opNorm _
      _ ≤ ‖toPhys‖ * (τ ^ (-(1 / (2 * α))) * ‖ψ‖) := mul_le_mul_of_nonneg_left hPn hT
      _ ≤ (‖toPhys‖ + ‖velocity‖ + 1) * τ ^ (-(1 / (2 * α))) * ‖ψ‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hk hψ)
  · rw [eLpNorm_congr_ae hae, ← Lp.norm_def]
    calc ‖velocity ⟨_, hmem⟩‖ ≤ ‖velocity‖ * ‖(⟨_, hmem⟩ : X)‖ := velocity.le_opNorm _
      _ ≤ ‖velocity‖ * (τ ^ (-(1 / α)) * ‖ψ‖) := mul_le_mul_of_nonneg_left hXn hV
      _ ≤ (‖toPhys‖ + ‖velocity‖ + 1) * τ ^ (-(1 / α)) * ‖ψ‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hi hψ)

end Breakdown.Freq
