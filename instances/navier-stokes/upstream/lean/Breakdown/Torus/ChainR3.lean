import Breakdown.Torus.StatementsInverse
import Breakdown.Transfer.VarConstIntegral

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ChainR3.Internal

theorem extendPiece_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} (hL : 0 ≤ L)
    (f : Piece X L) (σ : ℝ) : extendPiece f σ = f (projIcc 0 L hL σ) := by
  rw [extendPiece, dif_pos hL]
  rfl

theorem integral_congr_Ioo {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : ℝ → X} {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ σ ∈ Ioo 0 s, f σ = g σ) : ∫ σ in (0 : ℝ)..s, f σ = ∫ σ in (0 : ℝ)..s, g σ := by
  rw [intervalIntegral.integral_of_le hs, intervalIntegral.integral_of_le hs,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

theorem seqOp_comp (hS : SeqOpSpec) {E Y X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : ℕ → Y →L[ℝ] X) (B : ℕ → E →L[ℝ] Y) (CA CB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hA : ∀ n, ‖A n‖ ≤ CA) (hB : ∀ n, ‖B n‖ ≤ CB) :
    (seqOp A).comp (seqOp B) = seqOp fun n => (A n).comp (B n) := by
  have hAB : ∀ n, ‖(A n).comp (B n)‖ ≤ CA * CB := fun n =>
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hA n) (hB n) (norm_nonneg _) hCA)
  have e1 := (hS _ _ A CA hA hCA).1
  have e2 := (hS _ _ B CB hB hCB).1
  have e3 := (hS _ _ _ (CA * CB) hAB (mul_nonneg hCA hCB)).1
  refine ContinuousLinearMap.ext fun g => lp.ext (funext fun n => ?_)
  rw [ContinuousLinearMap.comp_apply, e1, e2, e3, ContinuousLinearMap.comp_apply]


theorem continuous_extendPiece {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} (hL : 0 ≤ L)
    (f : Piece X L) : Continuous (extendPiece f) := by
  have h : extendPiece f = IccExtend hL f := funext fun σ => by rw [extendPiece, dif_pos hL]
  rw [h]
  exact continuous_IccExtend_iff.2 f.continuous

theorem norm_extendPiece_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} (hL : 0 ≤ L)
    (f : Piece X L) (σ : ℝ) : ‖extendPiece f σ‖ ≤ ‖f‖ := by
  rw [extendPiece_eq hL]
  exact f.norm_coe_le_norm _

theorem lambda_bound {C : ℝ} (hC0 : 0 ≤ C)
    (hCb : ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → ∀ ζ : ShellData,
      ‖lambdaR3 φ hφ b τ ζ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖)
    (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) :
    ∀ τ, 0 < τ → τ ≤ 1 → ‖lambdaR3 φ hφ b τ‖ ≤ (C * ‖Freq.embedX φ‖) * τ ^ (-(3 / 4 : ℝ)) := by
  intro τ hτ _
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC0 (norm_nonneg _)) (rpow_nonneg hτ.le _)) fun ζ => ?_
  calc _ ≤ _ := hCb φ hφ b τ hτ ζ
    _ = _ := by ring

theorem lambda_cont (hH : ∀ A : Freq.L2R, ContinuousOn (fun τ => Freq.heatDivFree τ A) (Ioi 0))
    (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData) :
    ContinuousOn (fun τ => lambdaR3 φ hφ b τ ζ) (Ioi 0) :=
  (hH (advectShell φ hφ b ζ)).neg

theorem piece_eq (hF : R3Factor) (hLb : R3LambdaBound) (hC : PieceCompSpec) (hV : PieceConvSpec)
    (hP : PieceOperatorStatement)
    (hH : ∀ A : Freq.L2R, ContinuousOn (fun τ => Freq.heatDivFree τ A) (Ioi 0))
    (H : HeatBilinear Freq.X) (hK : H.K = Freq.bilinX) {L b : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1)
    (A : Approximant L b) (n : ℕ) :
    (∑ l, pieceConv L (fun τ => lambdaR3 (A.field n l) (A.isTest n l) b τ) (A.weight n l)).comp
      (pieceComp L (restrictR3 b)) = (2 : ℝ) • H.pieceBil L (A.r3Piece n) := by
  obtain ⟨C, hC0, hCb⟩ := hLb
  have hconv := fun l => (hV _ _ L _ (A.weight n l) _ hL0 hL1
    (mul_nonneg hC0 (norm_nonneg (Freq.embedX (A.field n l))))
    (lambda_bound hC0 hCb (A.field n l) (A.isTest n l) b) (lambda_cont hH (A.field n l) (A.isTest n l) b)).1
  have hcomp := (hC _ _ L (restrictR3 b) hL0.le).1
  have hbil := (hP _ H L hL0).1
  have hext : ∀ (g : Piece Freq.X L) σ, extendPiece (pieceComp L (restrictR3 b) g) σ =
      restrictR3 b (extendPiece g σ) := fun g σ => by
    rw [extendPiece_eq hL0.le (pieceComp L (restrictR3 b) g) σ, hcomp, ← extendPiece_eq hL0.le g σ]
  have hr : ∀ σ, extendPiece (A.r3Piece n) σ =
      ∑ l, extendPiece (A.weight n l) σ • Freq.embedX (A.field n l) := fun σ => by
    simp only [extendPiece_eq hL0.le]
    rfl
  refine ContinuousLinearMap.ext fun g => ContinuousMap.ext fun s => ?_
  have hint : ∀ l, IntervalIntegrable (fun σ => H.K ((s : ℝ) - σ)
      (extendPiece (A.weight n l) σ • Freq.embedX (A.field n l)) (extendPiece g σ)) volume 0 s := by
    intro l
    refine (varConstIntegral Freq.X H (fun σ => extendPiece (A.weight n l) σ • Freq.embedX (A.field n l))
      (extendPiece g) 0 L (‖A.weight n l‖ * ‖Freq.embedX (A.field n l)‖) ‖g‖ hL0.le
      (by exact ((continuous_extendPiece hL0.le (A.weight n l)).smul continuous_const).continuousOn)
      (continuous_extendPiece hL0.le g).continuousOn (fun σ _ => ?_)
      (fun σ _ => norm_extendPiece_le hL0.le g σ)).1 s s.2
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_extendPiece_le hL0.le _ σ) (norm_nonneg _)
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply,
    _root_.smul_apply, ContinuousMap.smul_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  simp only [hbil]
  simp_rw [hr, map_sum, _root_.sum_apply]
  have hsum := intervalIntegral.integral_finsetSum (μ := volume) (a := 0) (b := (s : ℝ)) (s := Finset.univ) (fun l _ => hint l)
  beta_reduce at hsum
  simp only [hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine (hconv l _ s).trans ?_
  refine (integral_congr_Ioo s.2.1 fun σ hσ => ?_).trans (intervalIntegral.integral_smul (2 : ℝ) (fun x => H.K ((s : ℝ) - x) (extendPiece (A.weight n l) x • Freq.embedX (A.field n l)) (extendPiece g x)))
  simp only [hext, hK, map_smul, _root_.smul_apply]
  exact (congrArg (fun x => extendPiece (A.weight n l) σ • x) (hF (A.field n l) (A.isTest n l) b (A.support n l) ((s : ℝ) - σ) (by linarith [hσ.2]) (extendPiece g σ))).symm.trans (smul_comm _ _ _)

theorem lambda_restrict (hF : R3Factor) (hLb : R3LambdaBound) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hV : PieceConvSpec) (hP : PieceOperatorStatement)
    (hH : ∀ A : Freq.L2R, ContinuousOn (fun τ => Freq.heatDivFree τ A) (Ioi 0))
    (H : HeatBilinear Freq.X) (hK : H.K = Freq.bilinX) {L b : ℝ} (hL0 : 0 < L) (hL1 : L ≤ 1)
    (A : Approximant L b) :
    (r3Lambda A).comp (r3Restrict L b) = seqOp fun n => (2 : ℝ) • H.pieceBil L (A.r3Piece n) := by
  obtain ⟨C, hC0, hCb⟩ := hLb
  have hbd := A.bound
  obtain ⟨D0, hD0⟩ := hbd
  have hDn : 0 ≤ max D0 0 := le_max_right _ _
  have hL4 : 0 ≤ L ^ (1 / 4 : ℝ) := rpow_nonneg hL0.le _
  have hA : ∀ n, ‖∑ l, pieceConv L (fun τ => lambdaR3 (A.field n l) (A.isTest n l) b τ) (A.weight n l)‖ ≤
      ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    refine ((hV _ _ L _ (A.weight n l) _ hL0 hL1 (mul_nonneg hC0 (norm_nonneg (Freq.embedX (A.field n l))))
      (lambda_bound hC0 hCb (A.field n l) (A.isTest n l) b)
      (lambda_cont hH (A.field n l) (A.isTest n l) b)).2).trans ?_
    have h1 : ‖Freq.embedX (A.field n l)‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).1
    have h2 : ‖A.weight n l‖ ≤ max D0 0 := le_max_of_le_left (hD0 n l).2
    exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h1 hC0) (by norm_num)) hL4) h2 (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hC0 hDn)) hL4)
  have hB : ∀ _n : ℕ, ‖pieceComp L (restrictR3 b)‖ ≤ ‖restrictR3 b‖ :=
    fun _ => (hC _ _ L (restrictR3 b) hL0.le).2
  have hsum0 : 0 ≤ ∑ _l : Fin A.terms, 4 * (C * max D0 0) * L ^ (1 / 4 : ℝ) * max D0 0 :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hC0 hDn)) hL4) hDn
  refine (seqOp_comp hS _ _ _ _ hsum0 (norm_nonneg _) hA hB).trans ?_
  exact congrArg seqOp (funext fun n => piece_eq hF ⟨C, hC0, hCb⟩ hC hV hP hH H hK hL0 hL1 A n)

end ChainR3.Internal

open ChainR3.Internal

theorem r3ChainEq (hF : R3Factor) (hL : R3LambdaBound) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hV : PieceConvSpec) (hP : PieceOperatorStatement)
    (hH : ∀ A : Freq.L2R, ContinuousOn (fun τ => Freq.heatDivFree τ A) (Ioi 0)) : R3ChainEq := by
  intro F hK P k θ b E _ _ J A hL0 hL1
  have key := lambda_restrict hF hL hS hC hV hP hH F.toHeatBilinear hK hL0 hL1 A
  simp only [chainOp, r3Op, key]

end Breakdown.Periodic
