import Breakdown.Torus.Basic
import Breakdown.Torus.StatementsAnalysis
import Breakdown.Transfer.StatementsDefs

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

def stepFrame (hK : KernelSharpBound) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) : HeatBilinear V where
  G t := heat (μ * t)
  G_zero := by
    show heat (μ * 0) = ContinuousLinearMap.id ℝ V
    rw [mul_zero, heat_zero]
  G_add := by
    intro s t hs ht
    show heat (μ * (s + t)) = (heat (μ * s)).comp (heat (μ * t))
    rw [mul_add]
    exact heat_add _ _ (mul_nonneg hμ.le hs) (mul_nonneg hμ.le ht)
  G_norm := fun t _ => norm_heat_le (μ * t)
  G_cont := by
    intro x
    exact (heat_continuousOn x).comp (continuous_const.mul continuous_id).continuousOn
      (fun t ht => mem_Ici.mpr (mul_nonneg hμ.le (mem_Ici.mp ht)))
  K τ := (μ ^ (3 / 4 : ℝ)) • kernel (μ * τ)
  K_symm := by
    intro τ u v
    show ((μ ^ (3 / 4 : ℝ)) • kernel (μ * τ)) u v = ((μ ^ (3 / 4 : ℝ)) • kernel (μ * τ)) v u
    simp only [smul_apply]
    rw [kernel_symm]
  CK := hK.choose
  K_bound := by
    intro τ hτ hτ1
    show ‖(μ ^ (3 / 4 : ℝ)) • kernel (μ * τ)‖ ≤ hK.choose * τ ^ (-(3 / 4 : ℝ))
    have hb := hK.choose_spec.2 (μ * τ) (mul_pos hμ hτ) (mul_le_one₀ hμ1 hτ.le hτ1)
    have hc : 0 ≤ μ ^ (3 / 4 : ℝ) := Real.rpow_nonneg hμ.le _
    have e : μ ^ (3 / 4 : ℝ) * (μ * τ) ^ (-(3 / 4 : ℝ)) = τ ^ (-(3 / 4 : ℝ)) := by
      rw [Real.mul_rpow hμ.le hτ.le, ← mul_assoc, ← Real.rpow_add hμ]
      norm_num
    rw [norm_smul, Real.norm_of_nonneg hc]
    calc μ ^ (3 / 4 : ℝ) * ‖kernel (μ * τ)‖
        ≤ μ ^ (3 / 4 : ℝ) * (hK.choose * (μ * τ) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hb hc
      _ = hK.choose * (μ ^ (3 / 4 : ℝ) * (μ * τ) ^ (-(3 / 4 : ℝ))) := by ring
      _ = hK.choose * τ ^ (-(3 / 4 : ℝ)) := by rw [e]
  K_cont := by
    intro u v
    show ContinuousOn (fun τ => ((μ ^ (3 / 4 : ℝ)) • kernel (μ * τ)) u v) (Ioi 0)
    simp only [smul_apply]
    exact ((kernel_continuousOn u v).comp (continuous_const.mul continuous_id).continuousOn
      (fun τ hτ => mem_Ioi.mpr (mul_pos hμ (mem_Ioi.mp hτ)))).const_smul (μ ^ (3 / 4 : ℝ))
  K_shift := by
    intro s τ hs hτ u v
    show heat (μ * s) (((μ ^ (3 / 4 : ℝ)) • kernel (μ * τ)) u v) =
      ((μ ^ (3 / 4 : ℝ)) • kernel (μ * (s + τ))) u v
    simp only [smul_apply, ContinuousLinearMap.map_smul]
    rw [heat_kernel _ _ (mul_nonneg hμ.le hs) (mul_pos hμ hτ), mul_add]

def stepScale (T lam : ℝ) (n : ℕ) : ℝ := T * lam ^ n

theorem stepScale_pos {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (n : ℕ) : 0 < stepScale T lam n :=
  mul_pos hT (pow_pos hl n)

theorem stepScale_le_one {T lam : ℝ} (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (n : ℕ) :
    stepScale T lam n ≤ 1 :=
  mul_le_one₀ hT1 (pow_nonneg hl.le n) (pow_le_one₀ hl.le hl1)

def stepStart (T lam : ℝ) (n : ℕ) : ℝ := T - stepScale T lam n

def stepNumber (T lam t : ℝ) : ℕ := ⌊Real.log ((T - t) / T) / Real.log lam⌋₊

def gluePieces (T lam : ℝ) (u : ℕ → Piece V (1 - lam)) (t : ℝ) : V :=
  (stepScale T lam (stepNumber T lam t)) ^ (-(1 / 4 : ℝ)) •
    extendPiece (u (stepNumber T lam t))
      ((t - stepStart T lam (stepNumber T lam t)) / stepScale T lam (stepNumber T lam t))

def GlueMild : Prop :=
  ∀ (hK : KernelSharpBound) (T lam : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam < 1)
    (u : ℕ → Piece V (1 - lam)),
    (∀ n, (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1.le n)).IsMildOnIcc
        (extendPiece (u n)) 0 (1 - lam)) →
    (∀ n, extendPiece (u (n + 1)) 0 = lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (u n)) →
    IsMildOn (gluePieces T lam u) 0 T ∧
      ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) (1 - lam),
        gluePieces T lam u (stepStart T lam n + stepScale T lam n * s) =
          (stepScale T lam n) ^ (-(1 / 4 : ℝ)) • extendPiece (u n) s

def SeqPerturbation : Prop :=
  ∀ (X E : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℕ → HeatBilinear X) (L θ c CK M ρ : ℝ) (ub res : ℕ → Piece X L) (J : E →L[ℝ] X)
    (R : lp (fun _ : ℕ => Piece X L) ∞ →L[ℝ] E × lp (fun _ : ℕ => Piece X L) ∞) (ξ : X),
    0 < L → L ≤ 1 → 0 < θ → θ < 1 → 0 ≤ CK → (∀ n, (H n).CK ≤ CK) → (∀ n, ‖ub n‖ ≤ M) →
    (∀ n, extendPiece (ub (n + 1)) 0 = c • pieceEnd L (ub n)) →
    (∀ n, ub n = (H n).pieceFree L (extendPiece (ub n) 0) + (H n).pieceBil L (ub n) (ub n) + res n) →
    (∀ n, ‖res n‖ ≤ θ ^ n * ρ) →
    (∀ g n, (R g).2 n - (2 : ℝ) • (H n).pieceBil L (ub n) ((R g).2 n) -
      (if n = 0 then (H 0).pieceFree L (J (R g).1)
        else (c / θ) • (H n).pieceFree L (pieceEnd L ((R g).2 (n - 1)))) = g n) →
    64 * ‖R‖ ^ 2 * CK * L ^ (1 / 4 : ℝ) * (ρ + ‖ξ‖) ≤ 1 →
    ∃ (e : E) (z : ℕ → Piece X L),
      (∀ n, ‖z n‖ ≤ 2 * ‖R‖ * (ρ + ‖ξ‖)) ∧ ‖e‖ ≤ 2 * ‖R‖ * (ρ + ‖ξ‖) ∧
      (∀ n, (H n).IsMildOnIcc (extendPiece (ub n + θ ^ n • z n)) 0 L) ∧
      extendPiece (z 0) 0 = ξ + J e ∧
      ∀ n, extendPiece (ub (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 = c • pieceEnd L (ub n + θ ^ n • z n)

def GlueUnbounded : Prop :=
  ∀ (T lam θ c₀ Z : ℝ) (u ub : ℕ → Piece V (1 - lam)) (z : ℕ → Piece V (1 - lam)),
    0 < T → 0 < lam → lam < 1 → 0 < θ → θ < 1 → 0 < c₀ →
    (∀ n, ∀ s : Icc (0 : ℝ) (1 - lam), c₀ ≤ ‖ub n s‖) → (∀ n, ‖z n‖ ≤ Z) →
    (∀ n, u n = ub n + θ ^ n • z n) →
    ¬ BddAbove ((fun t => ‖gluePieces T lam u t‖) '' Ico 0 T)

end Breakdown.Periodic
