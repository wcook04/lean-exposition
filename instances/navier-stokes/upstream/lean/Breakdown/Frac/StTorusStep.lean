import Breakdown.Frac.TorusHeat
import Breakdown.Frac.TorusKernel
import Breakdown.Frac.TorusKernelBound
import Breakdown.Torus.StatementsSteps
import Breakdown.Frac.StRealize

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

def fracStepCK (α : ℝ) (hα : 1 < α) : ℝ :=
  (fracTorusKernelSharpBound_of α hα (fracTorusKernelAlgebra α hα.le (fracTorusHeatAlgebra α))).choose

theorem fracStepCK_spec (α : ℝ) (hα : 1 < α) : 0 < fracStepCK α hα ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    ‖fracTorusKernel α τ‖ ≤ fracStepCK α hα * τ ^ (-(3 / (4 * α))) :=
  (fracTorusKernelSharpBound_of α hα (fracTorusKernelAlgebra α hα.le (fracTorusHeatAlgebra α))).choose_spec

def fracStepFrame (α : ℝ) (hα : 1 < α) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) : HeatBilinear V where
  G t := fracTorusHeat α (μ * t)
  G_zero := by
    show fracTorusHeat α (μ * 0) = ContinuousLinearMap.id ℝ V
    rw [mul_zero]
    exact (fracTorusHeatAlgebra α).2.1
  G_add := by
    intro s t hs ht
    show fracTorusHeat α (μ * (s + t)) = (fracTorusHeat α (μ * s)).comp (fracTorusHeat α (μ * t))
    rw [mul_add]
    exact (fracTorusHeatAlgebra α).2.2.1 _ _ (mul_nonneg hμ.le hs) (mul_nonneg hμ.le ht)
  G_norm := fun t _ => (fracTorusHeatAlgebra α).2.2.2.1 (μ * t)
  G_cont := by
    intro x
    exact (((fracTorusHeatAlgebra α).2.2.2.2.2 x).comp (continuous_const.mul continuous_id)).continuousOn
  K τ := (μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * τ)
  K_symm := by
    intro τ u v
    show ((μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * τ)) u v =
      ((μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * τ)) v u
    simp only [smul_apply]
    rw [(fracTorusKernelAlgebra α hα.le (fracTorusHeatAlgebra α)).2.1]
  CK := fracStepCK α hα
  K_bound := by
    intro τ hτ hτ1
    have hS := fracStepCK_spec α hα
    have hb := hS.2 (μ * τ) (mul_pos hμ hτ) (mul_le_one₀ hμ1 hτ.le hτ1)
    have hc : 0 ≤ μ ^ (3 / (4 * α)) := Real.rpow_nonneg hμ.le _
    have hα0 : 0 < α := by linarith
    have e : μ ^ (3 / (4 * α)) * (μ * τ) ^ (-(3 / (4 * α))) = τ ^ (-(3 / (4 * α))) := by
      rw [Real.mul_rpow hμ.le hτ.le, ← mul_assoc, ← Real.rpow_add hμ]
      simp
    have hexp : τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hτ hτ1
      have : 3 / (4 * α) ≤ 3 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    show ‖(μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * τ)‖ ≤ fracStepCK α hα * τ ^ (-(3 / 4 : ℝ))
    rw [norm_smul, Real.norm_of_nonneg hc]
    calc μ ^ (3 / (4 * α)) * ‖fracTorusKernel α (μ * τ)‖
        ≤ μ ^ (3 / (4 * α)) * (fracStepCK α hα * (μ * τ) ^ (-(3 / (4 * α)))) :=
          mul_le_mul_of_nonneg_left hb hc
      _ = fracStepCK α hα * (μ ^ (3 / (4 * α)) * (μ * τ) ^ (-(3 / (4 * α)))) := by ring
      _ = fracStepCK α hα * τ ^ (-(3 / (4 * α))) := by rw [e]
      _ ≤ fracStepCK α hα * τ ^ (-(3 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hexp hS.1.le
  K_cont := by
    intro u v
    show ContinuousOn (fun τ => ((μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * τ)) u v) (Ioi 0)
    simp only [smul_apply]
    exact (((fracTorusKernelAlgebra α hα.le (fracTorusHeatAlgebra α)).2.2.1 u v).comp
      (continuous_const.mul continuous_id).continuousOn
      (fun τ hτ => mem_Ioi.mpr (mul_pos hμ (mem_Ioi.mp hτ)))).const_smul (μ ^ (3 / (4 * α)))
  K_shift := by
    intro s τ hs hτ u v
    show fracTorusHeat α (μ * s) (((μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * τ)) u v) =
      ((μ ^ (3 / (4 * α))) • fracTorusKernel α (μ * (s + τ))) u v
    simp only [smul_apply, ContinuousLinearMap.map_smul]
    rw [(fracTorusKernelAlgebra α hα.le (fracTorusHeatAlgebra α)).2.2.2 _ _ (mul_nonneg hμ.le hs)
      (mul_pos hμ hτ), mul_add]

def fracGluePieces (α T lam : ℝ) (u : ℕ → Piece V (1 - lam)) (t : ℝ) : V :=
  (stepScale T lam (stepNumber T lam t)) ^ (-dilExponent α) •
    extendPiece (u (stepNumber T lam t))
      ((t - stepStart T lam (stepNumber T lam t)) / stepScale T lam (stepNumber T lam t))

def FracGlueMild (α : ℝ) (hα : 1 < α) : Prop :=
  ∀ (T lam : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam < 1)
    (u : ℕ → Piece V (1 - lam)),
    (∀ n, (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1.le n)).IsMildOnIcc
        (extendPiece (u n)) 0 (1 - lam)) →
    (∀ n, extendPiece (u (n + 1)) 0 = lam ^ dilExponent α • pieceEnd (1 - lam) (u n)) →
    IsFracTorusMildOn α (fracGluePieces α T lam u) 0 T ∧
      ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) (1 - lam),
        fracGluePieces α T lam u (stepStart T lam n + stepScale T lam n * s) =
          (stepScale T lam n) ^ (-dilExponent α) • extendPiece (u n) s

def FracGlueUnbounded (α : ℝ) : Prop :=
  ∀ (T lam θ c₀ Z : ℝ) (u ub : ℕ → Piece V (1 - lam)) (z : ℕ → Piece V (1 - lam)),
    0 < T → 0 < lam → lam < 1 → 0 < θ → θ < 1 → 0 < c₀ →
    (∀ n, ∀ s : Icc (0 : ℝ) (1 - lam), c₀ ≤ ‖ub n s‖) → (∀ n, ‖z n‖ ≤ Z) →
    (∀ n, u n = ub n + θ ^ n • z n) →
    ¬ BddAbove ((fun t => ‖fracGluePieces α T lam u t‖) '' Ico 0 T)

end Breakdown.Periodic
