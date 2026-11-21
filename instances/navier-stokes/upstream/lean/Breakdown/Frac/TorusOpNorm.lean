import Breakdown.Frac.StTorusInverse
import Breakdown.Torus.OpBounds

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusOpNorm.Internal

open OpBounds.Internal

theorem rpow_exponent_le {α τ : ℝ} (hα : 1 < α) (h0 : 0 < τ) (h1 : τ ≤ 1) :
    τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_ge h0 h1
  have : 3 / (4 * α) ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem bound_exponent_le {α C e z τ : ℝ} (hα : 1 < α) (hC : 0 ≤ C) (he : 0 ≤ e) (hz : 0 ≤ z)
    (h0 : 0 < τ) (h1 : τ ≤ 1) :
    C * τ ^ (-(3 / (4 * α))) * e * z ≤ C * τ ^ (-(3 / 4 : ℝ)) * e * z :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rpow_exponent_le hα h0 h1) hC) he) hz

theorem fracLambdaR3_sum (α : ℝ) {m : ℕ} (c : Fin m → ℝ) (φ : Fin m → Space → Space)
    (h : ∀ l, IsTestField (φ l)) (b τ : ℝ) (ζ : ShellData) :
    ∑ l, c l • fracLambdaR3 α (φ l) (h l) b τ ζ =
      fracLambdaR3 α (∑ l, c l • φ l) (isTestField_sum c φ h Finset.univ) b τ ζ := by
  simp only [fracLambdaR3, _root_.neg_apply, ContinuousLinearMap.comp_apply]
  rw [advectShell_sum c φ h b ζ Finset.univ]
  simp only [map_sum, map_smul, smul_neg, Finset.sum_neg_distrib]

theorem fracLambdaTorus_sum (α : ℝ) {m : ℕ} (c : Fin m → ℝ) (φ : Fin m → Space → Space)
    (h : ∀ l, IsTestField (φ l)) (b μ τ : ℝ) (ζ : ShellData) :
    ∑ l, c l • fracLambdaTorus α (φ l) (h l) b μ τ ζ =
      fracLambdaTorus α (∑ l, c l • φ l) (isTestField_sum c φ h Finset.univ) b μ τ ζ := by
  simp only [fracLambdaTorus, _root_.neg_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply]
  rw [advectShell_sum c φ h b ζ Finset.univ]
  simp only [map_sum, map_smul, smul_neg, Finset.sum_neg_distrib, Finset.smul_sum]
  refine congrArg Neg.neg (Finset.sum_congr rfl fun l _ => ?_)
  rw [smul_comm]

theorem isShellScale_simStep {α T lam b : ℝ} (hα : 0 < α) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) (hb : 0 < b) (hsb : Real.sqrt (simScale α T) * b ≤ 1 / 8) (n : ℕ) :
    IsShellScale (simScale α (stepScale T lam n)) b := by
  have hp := stepScale_pos hT hl n
  have hle : stepScale T lam n ≤ T := by
    show T * lam ^ n ≤ T
    exact mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1)
  have he : 0 ≤ 1 / α := by positivity
  refine ⟨Real.rpow_pos_of_pos hp _, Real.rpow_le_one hp.le (stepScale_le_one hT1 hl hl1 n) he, hb, ?_⟩
  have h : simScale α (stepScale T lam n) ≤ simScale α T :=
    Real.rpow_le_rpow hp.le hle he
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) hb.le).trans hsb

theorem norm_scaledDil_le {κ : ℝ} (F : ScaledMildFramework Freq.X κ) {μ : ℝ} (hμ : 0 < μ) :
    ‖F.D μ‖ ≤ μ ^ κ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hμ.le _) fun u => (F.D_norm μ hμ u).le

set_option maxHeartbeats 2000000 in
theorem norm_fracR3Shift_entry {κ : ℝ} (F : ScaledMildFramework Freq.X κ) (P : ℝ) (k : ℕ) {θ : ℝ}
    (hθ : 0 < θ) :
    ‖θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)‖ ≤ Real.exp (-(P / k)) ^ κ / θ := by
  have h1 : ‖F.stepFree P k‖ ≤ 1 := norm_pieceFree_le F.toHeatBilinear _
  have h2 : ‖F.stepEnd P k‖ ≤ Real.exp (-(P / k)) ^ κ := by
    show ‖(F.D (Real.exp (-(P / k)))).comp (pieceEnd (MildFramework.stepLength P k))‖ ≤ _
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ Real.exp (-(P / k)) ^ κ * 1 :=
          mul_le_mul (norm_scaledDil_le F (Real.exp_pos _)) (norm_pieceEnd_le _) (norm_nonneg _)
            (Real.rpow_nonneg (Real.exp_pos _).le _)
      _ = _ := mul_one _
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hθ.le, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hθ.le)
  calc _ ≤ ‖F.stepFree P k‖ * ‖F.stepEnd P k‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * Real.exp (-(P / k)) ^ κ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end TorusOpNorm.Internal

set_option maxHeartbeats 4000000 in
open OpBounds.Internal TorusOpNorm.Internal in
theorem fracOperatorNormBounds (α : ℝ) (hα : 1 < α) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hV : PieceConvSpec) (hRL : FracR3LambdaBound α) (hTL : FracTorusLambdaBound α)
    (hRR : RestrictR3Bound) (hE : Freq.EmbedLinear) (hH : FracHeatSolenoidalContinuous α)
    (hF : FracSourceOpContinuous α) : FracOperatorNormBounds α hα := by
  obtain ⟨C1, hC1, hb1⟩ := hRL
  obtain ⟨C2, hC2, hb2⟩ := hTL
  obtain ⟨C3, hC3, hb3⟩ := hRR
  have hα0 : 0 < α := by linarith
  have hC4 := restrictTorusFun_bound.choose_spec.1
  set C4 := restrictTorusFun_bound.choose
  have hK : 0 ≤ max (max (4 * C1) (4 * C2)) (max C3 C4) :=
    le_max_of_le_right (le_max_of_le_left hC3)
  refine ⟨max (max (4 * C1) (4 * C2)) (max C3 C4), hK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L b M A hL hL1 hM
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hb1' : ∀ (φ : Space → Space) (hφ : IsTestField φ) (τ : ℝ), 0 < τ → τ ≤ 1 → ∀ z : ShellData,
        ‖fracLambdaR3 α φ hφ b τ z‖ ≤ C1 * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖z‖ :=
      fun φ hφ τ h0 h1 z => (hb1 φ hφ b τ h0 z).trans
        (bound_exponent_le hα hC1 (norm_nonneg _) (norm_nonneg _) h0 h1)
    have hn : ∀ n, ‖∑ l, pieceConv L (fun τ => fracLambdaR3 α (A.field n l) (A.isTest n l) b τ)
        (A.weight n l)‖ ≤ 4 * (C1 * M) := by
      intro n
      refine norm_sum_pieceConv_le hV hL hL1
        (fun l τ => fracLambdaR3 α (A.field n l) (A.isTest n l) b τ)
        (A.weight n) (fun l => C1 * ‖Freq.embedX (A.field n l)‖)
        (fun l => mul_nonneg hC1 (norm_nonneg _)) ?_ ?_ (C1 * M) (mul_nonneg hC1 hM0) ?_
      · intro l τ h0 h1
        refine ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (mul_nonneg hC1 (norm_nonneg _)) (Real.rpow_nonneg h0.le _)) fun z => ?_
        exact (hb1' _ _ τ h0 h1 z).trans (le_of_eq (by ring))
      · intro l z
        simp only [fracLambdaR3, _root_.neg_apply, ContinuousLinearMap.comp_apply]
        exact (hH _).neg
      · intro σ τ h0 h1 z
        show ‖∑ l, A.weight n l σ • fracLambdaR3 α (A.field n l) (A.isTest n l) b τ z‖ ≤ _
        rw [fracLambdaR3_sum α (fun l => A.weight n l σ) (A.field n) (A.isTest n) b τ z]
        refine (hb1' _ _ τ h0 h1 z).trans ?_
        rw [embedX_sum hE (fun l => A.weight n l σ) (A.field n) (A.isTest n) Finset.univ]
        have hr : ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ ≤ M :=
          (ContinuousMap.norm_coe_le_norm (A.r3Piece n) σ).trans (hM n)
        have hp : 0 ≤ C1 * τ ^ (-(3 / 4 : ℝ)) := mul_nonneg hC1 (Real.rpow_nonneg h0.le _)
        calc C1 * τ ^ (-(3 / 4 : ℝ)) * ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ * ‖z‖ ≤
            C1 * τ ^ (-(3 / 4 : ℝ)) * M * ‖z‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hp) (norm_nonneg _)
          _ = C1 * M * τ ^ (-(3 / 4 : ℝ)) * ‖z‖ := by ring
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ (4 * (C1 * M)) hn (by positivity)).2.1).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hM0
  · intro b T lam M A hT hT1 hl hl1 hb hsb hM
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hL : 0 < 1 - lam := by linarith
    have hL1 : 1 - lam ≤ 1 := by linarith
    have hμ := isShellScale_simStep hα0 hT hT1 hl hl1.le hb hsb
    have hμτ : ∀ n τ, 0 < τ → τ ≤ 1 → stepScale T lam n * τ ≤ 1 := fun n τ h0 h1 =>
      mul_le_one₀ (stepScale_le_one hT1 hl hl1.le n) h0.le h1
    have hb2' : ∀ (n : ℕ) (φ : Space → Space) (hφ : IsTestField φ) (τ : ℝ), 0 < τ → τ ≤ 1 →
        ∀ z : ShellData, ‖fracLambdaTorus α φ hφ b (stepScale T lam n) τ z‖ ≤
          C2 * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖z‖ :=
      fun n φ hφ τ h0 h1 z => (hb2 φ hφ b _ τ (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1.le n) (hμ n) h0 (hμτ n τ h0 h1) z).trans
        (bound_exponent_le hα hC2 (norm_nonneg _) (norm_nonneg _) h0 h1)
    have hn : ∀ n, ‖∑ l, pieceConv (1 - lam)
        (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
        (A.weight n l)‖ ≤ 4 * (C2 * M) := by
      intro n
      refine norm_sum_pieceConv_le hV hL hL1
        (fun l τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
        (A.weight n) (fun l => C2 * ‖Freq.embedX (A.field n l)‖)
        (fun l => mul_nonneg hC2 (norm_nonneg _)) ?_ ?_ (C2 * M) (mul_nonneg hC2 hM0) ?_
      · intro l τ h0 h1
        refine ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (mul_nonneg hC2 (norm_nonneg _)) (Real.rpow_nonneg h0.le _)) fun z => ?_
        exact (hb2' n _ _ τ h0 h1 z).trans (le_of_eq (by ring))
      · intro l z
        simp only [fracLambdaTorus, _root_.neg_apply, _root_.smul_apply,
          ContinuousLinearMap.comp_apply]
        exact ((hF _ _ (stepScale_pos hT hl n)).const_smul
          ((stepScale T lam n) ^ (-(1 / (4 * α))))).neg
      · intro σ τ h0 h1 z
        show ‖∑ l, A.weight n l σ •
          fracLambdaTorus α (A.field n l) (A.isTest n l) b (stepScale T lam n) τ z‖ ≤ _
        rw [fracLambdaTorus_sum α (fun l => A.weight n l σ) (A.field n) (A.isTest n) b _ τ z]
        refine (hb2' n _ _ τ h0 h1 z).trans ?_
        rw [embedX_sum hE (fun l => A.weight n l σ) (A.field n) (A.isTest n) Finset.univ]
        have hr : ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ ≤ M :=
          (ContinuousMap.norm_coe_le_norm (A.r3Piece n) σ).trans (hM n)
        have hp : 0 ≤ C2 * τ ^ (-(3 / 4 : ℝ)) := mul_nonneg hC2 (Real.rpow_nonneg h0.le _)
        calc C2 * τ ^ (-(3 / 4 : ℝ)) * ‖∑ l, A.weight n l σ • Freq.embedX (A.field n l)‖ * ‖z‖ ≤
            C2 * τ ^ (-(3 / 4 : ℝ)) * M * ‖z‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hp) (norm_nonneg _)
          _ = C2 * M * τ ^ (-(3 / 4 : ℝ)) * ‖z‖ := by ring
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ (4 * (C2 * M)) hn (by positivity)).2.1).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) hM0
  · intro L b hL
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ C3 (fun _ => (hC _ _ L _ hL.le).2.trans (hb3 b)) hC3).2.1).trans ?_
    exact le_max_of_le_right (le_max_left _ _)
  · intro b T lam hT hT1 hl hl1 hb hsb
    have hR : ∀ n, ‖restrictTorus (simScale α (stepScale T lam n)) b‖ ≤ C4 := fun n =>
      LinearMap.mkContinuous_norm_le _ hC4 _
    show ‖seqOp _‖ ≤ _
    refine ((hS _ _ _ C4 (fun n => (hC _ _ (1 - lam) _ (by linarith)).2.trans (hR n)) hC4).2.1).trans ?_
    exact le_max_of_le_right (le_max_right _ _)
  · intro F P k θ hP hk hθ
    have h0 : 0 ≤ Real.exp (-(P / k)) ^ dilExponent α / θ :=
      div_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) hθ.le
    unfold fracR3Shift
    exact ((hS _ _ (fun _ => (0 : Piece Freq.X (MildFramework.stepLength P k) →L[ℝ]
      Piece Freq.X (MildFramework.stepLength P k))) _ (fun _ => by rw [norm_zero]; exact h0) h0).2.2.1 _
      (fun _ => norm_fracR3Shift_entry F P k hθ)).2
  · intro T lam θ hT hT1 hl hl1 hθ
    have h0 : 0 ≤ lam ^ dilExponent α / θ := div_nonneg (Real.rpow_nonneg hl.le _) hθ.le
    unfold fracTorusShift
    exact ((hS _ _ (fun _ => (0 : Piece V (1 - lam) →L[ℝ] Piece V (1 - lam))) _
      (fun _ => by rw [norm_zero]; exact h0) h0).2.2.1 _
      (fun n => norm_torusShift_entry _ (1 - lam) _ h0)).2

end Breakdown.Periodic
