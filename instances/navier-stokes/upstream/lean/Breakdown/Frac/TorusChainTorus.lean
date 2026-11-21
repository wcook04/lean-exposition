import Breakdown.Frac.StTorusInverse
import Breakdown.Torus.ChainTorus
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusChainTorus.Internal

open ChainTorus.Internal

theorem simScale_pos {α μ : ℝ} (hμ : 0 < μ) : 0 < simScale α μ := rpow_pos_of_pos hμ _

theorem simScale_le_one {α μ : ℝ} (hα : 1 < α) (hμ : 0 < μ) (hμ1 : μ ≤ 1) : simScale α μ ≤ 1 :=
  rpow_le_one hμ.le hμ1 (by have : (0 : ℝ) < α := by linarith
                            positivity)

theorem simScale_mono {α μ T : ℝ} (hα : 1 < α) (hμ : 0 < μ) (h : μ ≤ T) : simScale α μ ≤ simScale α T :=
  rpow_le_rpow hμ.le h (by have : (0 : ℝ) < α := by linarith
                           positivity)

theorem isShellScale_fracStep {α T lam b : ℝ} (hα : 1 < α) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) (hb : 0 < b) (hTb : Real.sqrt (simScale α T) * b ≤ 1 / 8) (n : ℕ) :
    IsShellScale (simScale α (stepScale T lam n)) b := by
  have hμ := stepScale_pos hT hl n
  refine ⟨simScale_pos hμ, simScale_le_one hα hμ (stepScale_le_one hT1 hl hl1 n), hb, ?_⟩
  have h1 : stepScale T lam n ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1)
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (simScale_mono hα hμ h1)) hb.le).trans hTb

theorem fracLambdaTorus_continuousOn {α : ℝ} (hSC : FracSourceOpContinuous α) (φ : Space → Space)
    (hφ : IsTestField φ) (b : ℝ) {μ : ℝ} (hμ : 0 < μ) (ζ : ShellData) :
    ContinuousOn (fun τ => fracLambdaTorus α φ hφ b μ τ ζ) (Ioi 0) := by
  unfold fracLambdaTorus
  simp only [neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  exact ((hSC μ (advectShell φ hφ b ζ) hμ).const_smul (μ ^ (-(1 / (4 * α))))).neg

theorem rpow_exponent_compare {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_ge hτ hτ1
  have : 3 / (4 * α) ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

set_option maxHeartbeats 2000000 in
theorem fracChain_apply (α : ℝ) (hα : 1 < α) (hF : FracTorusFactor α) (hS : SeqOpSpec)
    (hC : PieceCompSpec) (hV : PieceConvSpec) (hP : PieceOperatorStatement)
    (hSC : FracSourceOpContinuous α) {T lam b : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (A : Approximant (1 - lam) b)
    (hlt : lam < 1) (hb : 0 < b) (hTb : Real.sqrt (simScale α T) * b ≤ 1 / 8) (CΛ : ℝ) (hCΛ0 : 0 ≤ CΛ)
    (hCΛ : ∀ (φ : Space → Space) (hφ : IsTestField φ) (b μ τ : ℝ), 0 < μ → μ ≤ 1 →
      IsShellScale (simScale α μ) b → 0 < τ → μ * τ ≤ 1 → ∀ ζ : ShellData,
        ‖fracLambdaTorus α φ hφ b μ τ ζ‖ ≤ CΛ * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖ζ‖)
    (CA : ℝ) (hCA : ∀ n l, ‖Freq.embedX (A.field n l)‖ ≤ CA ∧ ‖A.weight n l‖ ≤ CA) :
    ∀ g n, ((fracTorusLambda α A T lam).comp (fracTorusRestrict α (1 - lam) b T lam)) g n =
      ((2 : ℝ) • (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam)
          (A.torusPiece (simScale α (stepScale T lam n)) n)) (g n) := by
  have hCb0 : 0 ≤ max CA 0 := le_max_right _ _
  have hL0 : 0 < 1 - lam := by linarith
  have hL1 : 1 - lam ≤ 1 := by linarith
  have hq : 0 ≤ (1 - lam) ^ (1 / 4 : ℝ) := rpow_nonneg hL0.le _
  have hsh := isShellScale_fracStep hα hT hT1 hl hl1 hb hTb
  have hC0 : 0 ≤ CΛ * max CA 0 := mul_nonneg hCΛ0 hCb0
  have hΛb : ∀ n l τ, 0 < τ → τ ≤ 1 →
      ‖fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ‖ ≤
        CΛ * max CA 0 * τ ^ (-(3 / 4 : ℝ)) := by
    intro n l τ hτ hτ1
    have hr : 0 ≤ τ ^ (-(3 / 4 : ℝ)) := rpow_nonneg hτ.le _
    have hr' : 0 ≤ τ ^ (-(3 / (4 * α))) := rpow_nonneg hτ.le _
    have hcmp := rpow_exponent_compare hα hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 hr) fun ζ => ?_
    have h1 := hCΛ _ (A.isTest n l) b _ τ (stepScale_pos hT hl n) (stepScale_le_one hT1 hl hl1 n)
      (hsh n) hτ (mul_le_one₀ (stepScale_le_one hT1 hl hl1 n) hτ.le hτ1) ζ
    have h2 : ‖Freq.embedX (A.field n l)‖ ≤ max CA 0 := (hCA n l).1.trans (le_max_left _ _)
    calc _ ≤ _ := h1
      _ ≤ CΛ * τ ^ (-(3 / 4 : ℝ)) * max CA 0 * ‖ζ‖ := by
          gcongr
      _ = _ := by ring
  have hPC := fun n l => hV ShellData V (1 - lam)
    (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ) (A.weight n l)
    (CΛ * max CA 0) hL0 hL1 hC0 (hΛb n l)
    (fun ζ => fracLambdaTorus_continuousOn hSC _ _ _ (stepScale_pos hT hl n) ζ)
  have hBn : ∀ n, ‖∑ l, pieceConv (1 - lam)
      (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
        (A.weight n l)‖ ≤
        A.terms * (4 * (CΛ * max CA 0) * (1 - lam) ^ (1 / 4 : ℝ) * max CA 0) := by
    intro n
    calc _ ≤ ∑ l, ‖pieceConv (1 - lam)
          (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
            (A.weight n l)‖ := norm_sum_le _ _
      _ ≤ ∑ _l : Fin A.terms, 4 * (CΛ * max CA 0) * (1 - lam) ^ (1 / 4 : ℝ) * max CA 0 := by
          refine Finset.sum_le_sum fun l _ => (hPC n l).2.trans ?_
          exact mul_le_mul_of_nonneg_left ((hCA n l).2.trans (le_max_left _ _))
            (mul_nonneg (mul_nonneg (by norm_num) hC0) hq)
      _ = _ := by simp
  have hM0 : 0 ≤ (A.terms : ℝ) * (4 * (CΛ * max CA 0) * (1 - lam) ^ (1 / 4 : ℝ) * max CA 0) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hq) hCb0)
  have hTL := (hS (Piece ShellData (1 - lam)) (Piece V (1 - lam)) _ _ hBn hM0).1
  have hCr0 : 0 ≤ restrictTorusFun_bound.choose := restrictTorusFun_bound.choose_spec.1
  have hRb : ∀ n, ‖pieceComp (1 - lam) (restrictTorus (simScale α (stepScale T lam n)) b)‖ ≤
      restrictTorusFun_bound.choose := fun n =>
    (hC _ _ _ _ hL0.le).2.trans (LinearMap.mkContinuous_norm_le _ hCr0 _)
  have hTR := (hS (Piece V (1 - lam)) (Piece ShellData (1 - lam)) _ _ hRb hCr0).1
  intro g n
  refine ContinuousMap.ext fun s => ?_
  rw [ContinuousLinearMap.comp_apply]
  unfold fracTorusLambda fracTorusRestrict
  rw [hTL, hTR, torusPiece_eq_sum, map_sum]
  simp only [smul_apply, sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_sum, Finset.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(hPC n l).1, (hP V _ (1 - lam) hL0).1, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr_ae ?_
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  filter_upwards [Measure.ae_ne volume (s : ℝ)] with σ hne hmem
  rw [uIoc_of_le hs0] at hmem
  have hτ : 0 < (s : ℝ) - σ := sub_pos.2 (lt_of_le_of_ne hmem.2 hne)
  have hpc : extendPiece (pieceComp (1 - lam) (restrictTorus (simScale α (stepScale T lam n)) b) (g n)) σ =
      restrictTorus (simScale α (stepScale T lam n)) b (extendPiece (g n) σ) := by
    rw [ChainTorus.Internal.extend_eq hL0.le, ChainTorus.Internal.extend_eq hL0.le, (hC _ _ _ _ hL0.le).1]
  rw [hpc, ← hF _ (A.isTest n l) b _ (stepScale_pos hT hl n) (stepScale_le_one hT1 hl hl1 n) (hsh n)
    (A.support n l) _ hτ]
  show _ = (2 : ℝ) • (((stepScale T lam n) ^ (3 / (4 * α))) •
      fracTorusKernel α (stepScale T lam n * ((s : ℝ) - σ)))
    (extendPiece (weightedPiece (A.weight n l)
      ((simScale α (stepScale T lam n) ^ (1 / 4 : ℝ)) •
        toV (transplantField (simScale α (stepScale T lam n)) (A.field n l)))) σ)
    (extendPiece (g n) σ)
  rw [ChainTorus.Internal.extend_eq hL0.le (weightedPiece _ _), ChainTorus.Internal.extend_eq hL0.le (A.weight n l)]
  simp only [weightedPiece, ContinuousMap.coe_mk, map_smul, smul_apply, smul_smul]
  congr 1
  ring

end FracTorusChainTorus.Internal

open ChainTorus.Internal FracTorusChainTorus.Internal in
theorem fracTorusChainEq (α : ℝ) (hα : 1 < α) (hF : FracTorusFactor α) (hL : FracTorusLambdaBound α)
    (hS : SeqOpSpec) (hC : PieceCompSpec) (hV : PieceConvSpec) (hP : PieceOperatorStatement)
    (hSC : FracSourceOpContinuous α) : FracTorusChainEq α hα := by
  intro T lam θ b hT hT1 hl hl1 E _ _ Jt A hlt hb hTb
  have key : (fracTorusLambda α A T lam).comp (fracTorusRestrict α (1 - lam) b T lam) =
      seqOp fun n => (2 : ℝ) • (fracStepFrame α hα (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam)
          (A.torusPiece (simScale α (stepScale T lam n)) n) :=
    (seqOp_eq_of _ _ (fracChain_apply α hα hF hS hC hV hP hSC hT hT1 hl hl1 A hlt hb hTb hL.choose
      hL.choose_spec.1 hL.choose_spec.2 A.bound.choose A.bound.choose_spec)).symm
  simp only [chainOp, fracTorusOp, key]

end Breakdown.Periodic
