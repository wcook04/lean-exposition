import Breakdown.Frac.StTorusStepCompare
import Breakdown.Torus.CompareStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracCompareLambda.Internal

theorem sum_pieceConv_apply {Z X : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} {ι : Type} (u : Finset ι)
    (T : ι → Piece Z L →L[ℝ] Piece X L) (ζ : Piece Z L) (s : Icc (0 : ℝ) L) :
    (∑ l ∈ u, T l) ζ s = ∑ l ∈ u, T l ζ s := by
  rw [_root_.sum_apply]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply]

theorem rpow_exponent_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_ge hτ hτ1 ?_
  have h4 : (4 : ℝ) ≤ 4 * α := by linarith
  have : 3 / (4 * α) ≤ 3 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h4
  linarith

theorem simScale_pos {α μ : ℝ} (hμ : 0 < μ) : 0 < simScale α μ := rpow_pos_of_pos hμ _

theorem simScale_le_one {α μ : ℝ} (hα : 1 < α) (hμ : 0 < μ) (hμ1 : μ ≤ 1) : simScale α μ ≤ 1 :=
  rpow_le_one hμ.le hμ1 (by have : (0 : ℝ) < α := by linarith
                            positivity)

theorem simScale_mono {α μ T : ℝ} (hα : 1 < α) (hμ : 0 < μ) (h : μ ≤ T) :
    simScale α μ ≤ simScale α T :=
  rpow_le_rpow hμ.le h (by have : (0 : ℝ) < α := by linarith
                           positivity)

theorem isShellScale_step {α T lam b : ℝ} (hα : 1 < α) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) (hb : 0 < b) (hTb : Real.sqrt (simScale α T) * b ≤ 1 / 8) (n : ℕ) :
    IsShellScale (simScale α (stepScale T lam n)) b := by
  have hμ := stepScale_pos hT hl n
  refine ⟨simScale_pos hμ, simScale_le_one hα hμ (stepScale_le_one hT1 hl hl1 n), hb, ?_⟩
  have h1 : stepScale T lam n ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1)
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (simScale_mono hα hμ h1)) hb.le).trans hTb

theorem lambdaR3_continuousOn {α : ℝ} (hH : FracHeatSolenoidalContinuous α)
    (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData) :
    ContinuousOn (fun τ => fracLambdaR3 α φ hφ b τ ζ) (Ioi 0) :=
  (hH (advectShell φ hφ b ζ)).neg

theorem lambdaTorus_continuousOn {α : ℝ} (hSC : FracSourceOpContinuous α) (φ : Space → Space)
    (hφ : IsTestField φ) (b : ℝ) {μ : ℝ} (hμ : 0 < μ) (ζ : ShellData) :
    ContinuousOn (fun τ => fracLambdaTorus α φ hφ b μ τ ζ) (Ioi 0) := by
  unfold fracLambdaTorus
  simp only [neg_apply, smul_apply, ContinuousLinearMap.comp_apply]
  exact ((hSC μ (advectShell φ hφ b ζ) hμ).const_smul (μ ^ (-(1 / (4 * α))))).neg

end FracCompareLambda.Internal

open FracCompareLambda.Internal

set_option maxHeartbeats 400000 in
theorem fracR3LambdaFormula (α : ℝ) (hα : 1 < α) (hS : SeqOpSpec) (hV : PieceConvSpec)
    (hB : FracR3LambdaBound α) (hC : FracHeatSolenoidalContinuous α) : FracR3LambdaFormula α := by
  intro L b A hL0 hL1 ζ m s
  obtain ⟨C, hC0, hCb⟩ := hB
  obtain ⟨D0, hD0⟩ := A.bound
  have hD : 0 ≤ max D0 0 := le_max_right _ _
  have hq : 0 ≤ L ^ (1 / 4 : ℝ) := rpow_nonneg hL0.le _
  have hΛ : ∀ n l τ, 0 < τ → τ ≤ 1 →
      ‖fracLambdaR3 α (A.field n l) (A.isTest n l) b τ‖ ≤
        C * ‖Freq.embedX (A.field n l)‖ * τ ^ (-(3 / 4 : ℝ)) := by
    intro n l τ hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hC0 (norm_nonneg _)) (rpow_nonneg hτ.le _)) fun z => ?_
    have hr := rpow_exponent_le hα hτ hτ1
    calc _ ≤ _ := hCb _ (A.isTest n l) b τ hτ z
      _ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX (A.field n l)‖ * ‖z‖ := by gcongr
      _ = _ := by ring
  have hPC := fun n l => hV ShellData Freq.X L (fun τ => fracLambdaR3 α (A.field n l) (A.isTest n l) b τ)
    (A.weight n l) (C * ‖Freq.embedX (A.field n l)‖) hL0 hL1 (mul_nonneg hC0 (norm_nonneg _))
    (hΛ n l) (lambdaR3_continuousOn hC (A.field n l) (A.isTest n l) b)
  have hBn : ∀ n, ‖∑ l, pieceConv L (fun τ => fracLambdaR3 α (A.field n l) (A.isTest n l) b τ)
      (A.weight n l)‖ ≤ ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (hPC n l).2.trans ?_)
    have h1 : ‖Freq.embedX (A.field n l)‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).1
    have h2 : ‖A.weight n l‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).2
    gcongr
  have hM0 : 0 ≤ ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hTL := (hS (Piece ShellData L) (Piece Freq.X L) _ _ hBn hM0).1
  unfold fracR3Lambda
  rw [hTL, sum_pieceConv_apply]
  exact Finset.sum_congr rfl fun l _ => (hPC m l).1 (ζ m) s

set_option maxHeartbeats 400000 in
theorem fracTorusLambdaFormula (α : ℝ) (hα : 1 < α) (hS : SeqOpSpec) (hV : PieceConvSpec)
    (hB : FracTorusLambdaBound α) (hSC : FracSourceOpContinuous α) : FracTorusLambdaFormula α := by
  intro L b T lam A hL0 hL1 hT hT1 hl hl1 hb hTb ζ m s
  obtain ⟨C, hC0, hCb⟩ := hB
  obtain ⟨D0, hD0⟩ := A.bound
  have hD : 0 ≤ max D0 0 := le_max_right _ _
  have hq : 0 ≤ L ^ (1 / 4 : ℝ) := rpow_nonneg hL0.le _
  have hsh := isShellScale_step hα hT hT1 hl hl1 hb hTb
  have hΛ : ∀ n l τ, 0 < τ → τ ≤ 1 →
      ‖fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ‖ ≤
        C * ‖Freq.embedX (A.field n l)‖ * τ ^ (-(3 / 4 : ℝ)) := by
    intro n l τ hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hC0 (norm_nonneg _)) (rpow_nonneg hτ.le _)) fun z => ?_
    have hr := rpow_exponent_le hα hτ hτ1
    calc _ ≤ _ := hCb _ (A.isTest n l) b _ τ (stepScale_pos hT hl n)
          (stepScale_le_one hT1 hl hl1 n) (hsh n) hτ
          (mul_le_one₀ (stepScale_le_one hT1 hl hl1 n) hτ.le hτ1) z
      _ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX (A.field n l)‖ * ‖z‖ := by gcongr
      _ = _ := by ring
  have hPC := fun n l => hV ShellData V L
    (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
    (A.weight n l) (C * ‖Freq.embedX (A.field n l)‖) hL0 hL1 (mul_nonneg hC0 (norm_nonneg _))
    (hΛ n l) (fun z => lambdaTorus_continuousOn hSC _ _ _ (stepScale_pos hT hl n) z)
  have hBn : ∀ n, ‖∑ l, pieceConv L
      (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
        (A.weight n l)‖ ≤
        ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (hPC n l).2.trans ?_)
    have h1 : ‖Freq.embedX (A.field n l)‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).1
    have h2 : ‖A.weight n l‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).2
    gcongr
  have hM0 : 0 ≤ ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hTL := (hS (Piece ShellData L) (Piece V L) _ _ hBn hM0).1
  unfold fracTorusLambda
  rw [hTL, sum_pieceConv_apply]
  exact Finset.sum_congr rfl fun l _ => (hPC m l).1 (ζ m) s

end Breakdown.Periodic
