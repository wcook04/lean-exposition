import Breakdown.Frac.StTorusStepCompare
import Breakdown.Torus.CompareStatements
import Breakdown.Torus.SeqOps

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace TorusCompareEntryTorus.Internal

theorem shiftChain_self {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (B : ℕ → X →L[ℝ] X)
    (m : ℕ) : shiftChain B m m = ContinuousLinearMap.id ℝ X := by
  cases m with
  | zero => simp [shiftChain]
  | succ n => simp [shiftChain]

theorem sourceOp_apply {α : ℝ} (hE : FracSourceOpExists α) {μ : ℝ} (hμ : 0 < μ) (τ : ℝ)
    (A : Freq.L2R) : fracSourceOp α μ τ A =
      fracTorusForce α (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) := by
  have h := (hE μ τ).choose_spec A
  unfold fracSourceOp
  rw [dif_pos (hE μ τ), h]
  unfold fracSourceFun
  rw [if_pos hμ]

theorem heat_sourceOp {α : ℝ} (hF : FracTorusForceAlgebra α) (hE : FracSourceOpExists α) {μ t τ : ℝ}
    (hμ : 0 < μ) (ht : 0 ≤ t) (hτ : 0 < τ) (A : Freq.L2R) :
    fracTorusHeat α (μ * t) (fracSourceOp α μ τ A) = fracSourceOp α μ (t + τ) A := by
  rw [sourceOp_apply hE hμ, sourceOp_apply hE hμ,
    hF.2.1 (μ * τ) (μ * (t + τ)) (mul_pos hμ hτ) (by nlinarith),
    show μ * (t + τ) - μ * τ = μ * t by ring]

theorem heat_lambdaTorus {α : ℝ} (hF : FracTorusForceAlgebra α) (hE : FracSourceOpExists α)
    (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) {μ t τ : ℝ} (hμ : 0 < μ)
    (ht : 0 ≤ t) (hτ : 0 < τ) (ζ : ShellData) :
    fracTorusHeat α (μ * t) (fracLambdaTorus α φ hφ b μ τ ζ) = fracLambdaTorus α φ hφ b μ (t + τ) ζ := by
  simp only [fracLambdaTorus, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_neg, map_smul]
  rw [heat_sourceOp hF hE hμ ht hτ]

theorem lambdaTorus_continuousOn {α : ℝ} (hF : FracTorusForceAlgebra α) (hE : FracSourceOpExists α)
    (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) {μ : ℝ} (hμ : 0 < μ) (ζ : ShellData) :
    ContinuousOn (fun τ => fracLambdaTorus α φ hφ b μ τ ζ) (Ioi 0) := by
  have e : (fun τ => fracLambdaTorus α φ hφ b μ τ ζ) = fun τ =>
      -((μ ^ (-(1 / (4 * α)))) • fracTorusForce α (μ * τ)
        (fun x => ((advectShell φ hφ b ζ : Freq.L2R) : Space → Space) (simCoord (simScale α μ) x))) := by
    funext τ
    simp only [fracLambdaTorus, neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply]
    rw [sourceOp_apply hE hμ]
  have hc : ContinuousOn (fun τ : ℝ => fracTorusForce α (μ * τ)
      (fun x => ((advectShell φ hφ b ζ : Freq.L2R) : Space → Space) (simCoord (simScale α μ) x))) (Ioi 0) :=
    (hF.2.2 _).comp (continuous_const.mul continuous_id).continuousOn fun τ hτ => mul_pos hμ hτ
  rw [e]
  exact (hc.const_smul (μ ^ (-(1 / (4 * α))))).neg

theorem isShellScale_sim {α T lam b : ℝ} (hα : 1 < α) (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam)
    (hl1 : lam ≤ 1) (hb : 0 < b) (hTb : Real.sqrt (simScale α T) * b ≤ 1 / 8) (n : ℕ) :
    IsShellScale (simScale α (stepScale T lam n)) b := by
  have hα0 : 0 ≤ 1 / α := by positivity
  have hs0 := stepScale_pos hT hl n
  have hs1 := stepScale_le_one hT1 hl hl1 n
  have hsT : stepScale T lam n ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1)
  refine ⟨rpow_pos_of_pos hs0 _, rpow_le_one hs0.le hs1 hα0, hb, ?_⟩
  have h : simScale α (stepScale T lam n) ≤ simScale α T := rpow_le_rpow hs0.le hsT hα0
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) hb.le).trans hTb

theorem lambda_integrable {α : ℝ} (hα : 1 < α) (hF : FracTorusForceAlgebra α)
    (hE : FracSourceOpExists α) (hB : FracTorusLambdaBound α) {L b : ℝ} (A : Approximant L b) {μ : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hμ : IsShellScale (simScale α μ) b) (n : ℕ) (l : Fin A.terms)
    (ζ : Piece ShellData L) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    IntervalIntegrable (fun σ => extendPiece (A.weight n l) σ •
      fracLambdaTorus α (A.field n l) (A.isTest n l) b μ (u - σ) (extendPiece ζ σ)) volume 0 u := by
  obtain ⟨C, hC0, hC⟩ := hB
  have hK0 : 0 ≤ C * ‖Freq.embedX (A.field n l)‖ := mul_nonneg hC0 (norm_nonneg _)
  have hexp : -(3 / 4 : ℝ) ≤ -(3 / (4 * α)) := by
    have h1 : 3 / (4 * α) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  have hΛ : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ‖fracLambdaTorus α (A.field n l) (A.isTest n l) b μ τ‖ ≤
      (C * ‖Freq.embedX (A.field n l)‖) * τ ^ (-(3 / 4 : ℝ)) := by
    intro τ hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 (rpow_nonneg hτ.le _)) fun ζ => ?_
    have hr : τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := rpow_le_rpow_of_exponent_ge hτ hτ1 hexp
    calc _ ≤ C * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX (A.field n l)‖ * ‖ζ‖ :=
          hC _ (A.isTest n l) b μ τ hμ0 hμ1 hμ hτ (mul_le_one₀ hμ1 hτ.le hτ1) ζ
      _ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX (A.field n l)‖ * ‖ζ‖ := by gcongr
      _ = _ := by ring
  have h := SeqOps.Internal.convKernel_integrable
    (fun τ => fracLambdaTorus α (A.field n l) (A.isTest n l) b μ τ) (A.weight n l) hK0 hΛ
    (fun ζ => lambdaTorus_continuousOn hF hE _ _ _ hμ0 ζ) ζ u hu hu1
  have h2 := (h.comp_sub_left u).symm
  simp only [sub_zero, sub_self] at h2
  simpa only [SeqOps.Internal.convKernel, sub_sub_cancel] using h2

theorem scalar_split {lam θ κ : ℝ} (hl : 0 ≤ lam) (n : ℕ) :
    (lam ^ κ / θ) ^ n = (θ⁻¹) ^ n * (lam ^ n) ^ κ := by
  rw [div_eq_mul_inv, mul_pow, rpow_pow_comm hl, mul_comm]

theorem entry_pointwise {α : ℝ} (hF : FracTorusForceAlgebra α) (hE : FracSourceOpExists α)
    (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) {μ μ' c d θ' w t τ τ' : ℝ}
    (hμ : 0 < μ) (ht : 0 ≤ t) (hτ : 0 < τ) (hτ' : t + τ = τ') (hc : c = θ' * d) (ζ : ShellData) :
    w • ((restrictTorus μ' b).comp (c • fracTorusHeat α (μ * t))) (fracLambdaTorus α φ hφ b μ τ ζ) =
      θ' • (w • restrictTorus μ' b (d • -((μ ^ (-(1 / (4 * α)))) •
        fracSourceOp α μ τ' (advectShell φ hφ b ζ)))) := by
  show w • restrictTorus μ' b (c • fracTorusHeat α (μ * t) (fracLambdaTorus α φ hφ b μ τ ζ)) = _
  rw [heat_lambdaTorus hF hE φ hφ b hμ ht hτ, hτ', hc, map_smul, map_smul, smul_smul, smul_smul, smul_smul]
  simp only [fracLambdaTorus, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply]
  congr 1
  ring

theorem pieceEnd_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} (h : 0 ≤ L)
    (f : Piece X L) : pieceEnd L f = f ⟨L, h, le_rfl⟩ := by
  simp only [pieceEnd, dif_pos h]
  rfl

end TorusCompareEntryTorus.Internal

open TorusCompareEntryTorus.Internal in
theorem fracTorusEntryFormula (α : ℝ) (hα : 1 < α) (hCh : FracTorusChainFormula α hα)
    (hL : FracTorusLambdaFormula α) (hB : FracTorusLambdaBound α) (hF : FracTorusForceAlgebra α)
    (hE : FracSourceOpExists α) : FracTorusEntryFormula α hα := by
  intro T lam θ hT hT1 hl hl1 b A hlt hl2 hθ hb hTb ζ m j s
  have hL0 : 0 < 1 - lam := by linarith
  have hL1 : 1 - lam ≤ 1 := by linarith
  have hμ0 := stepScale_pos hT hl m
  have hμ1 := stepScale_le_one hT1 hl hl1 m
  have hsh : IsShellScale (simScale α (stepScale T lam m)) b := isShellScale_sim hα hT hT1 hl hl1 hb hTb m
  have hy := hL (1 - lam) b T lam A hL0 hL1 hT hT1 hl hl1 hb hTb ζ m
  have push : ∀ (Φ : V →L[ℝ] ShellData) (u : ℝ), 0 ≤ u → u ≤ 1 →
      Φ (∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ •
        fracLambdaTorus α (A.field m l) (A.isTest m l) b (stepScale T lam m) (u - σ) (extendPiece (ζ m) σ)) =
      ∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ •
        Φ (fracLambdaTorus α (A.field m l) (A.isTest m l) b (stepScale T lam m) (u - σ)
          (extendPiece (ζ m) σ)) := by
    intro Φ u hu hu1
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Φ
      (lambda_integrable hα hF hE hB A hμ0 hμ1 hsh m l (ζ m) hu hu1)]
    simp only [map_smul]
  have hyL : pieceEnd (1 - lam) (fracTorusLambda α A T lam ζ m) = ∑ l, ∫ σ in (0 : ℝ)..(1 - lam),
      extendPiece (A.weight m l) σ •
        fracLambdaTorus α (A.field m l) (A.isTest m l) b (stepScale T lam m) ((1 - lam) - σ)
          (extendPiece (ζ m) σ) :=
    (pieceEnd_eq hL0.le _).trans (hy ⟨1 - lam, hL0.le, le_rfl⟩)
  have e1 : ∀ i : ℕ, shiftChain (fracTorusStep α hα T lam θ hT hT1 hl hl1) m (m + (i + 1))
      (fracTorusLambda α A T lam ζ m) s =
      ((lam ^ dilExponent α / θ) ^ (i + 1) •
        fracTorusHeat α (stepScale T lam m * (lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1))))
        (pieceEnd (1 - lam) (fracTorusLambda α A T lam ζ m)) :=
    fun i => hCh T lam θ hT hT1 hl hl1 hlt (fracTorusLambda α A T lam ζ m) m i s
  rw [Finset.smul_sum]
  unfold fracTorusEntry
  rcases j with _ | i
  · refine (congrArg (restrictTorus (simScale α (stepScale T lam m)) b)
      ((congrArg (fun f : Piece V (1 - lam) →L[ℝ] Piece V (1 - lam) => f (fracTorusLambda α A T lam ζ m) s)
        (shiftChain_self (fracTorusStep α hα T lam θ hT hT1 hl hl1) m)).trans (hy s))).trans ?_
    refine (push _ s s.2.1 (s.2.2.trans hL1)).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pow_zero (θ⁻¹), one_smul, if_pos rfl]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    have e : (1 : ℝ) - σ - 1 * (1 - (s : ℝ)) = s - σ := by ring
    simp only [pow_zero lam, one_rpow, one_smul, e, add_zero]
    simp only [fracLambdaTorus, neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply]
  · have ht : 0 ≤ lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1) := by
      have h1 : lam ^ (i + 1) ≤ lam := pow_le_of_le_one hl.le hl1 (Nat.succ_ne_zero i)
      have h2 : 0 ≤ lam ^ (i + 1) * (s : ℝ) := mul_nonneg (pow_nonneg hl.le _) s.2.1
      linarith
    refine (congrArg (restrictTorus (simScale α (stepScale T lam (m + (i + 1)))) b) ((e1 i).trans
      (congrArg (⇑((lam ^ dilExponent α / θ) ^ (i + 1) •
        fracTorusHeat α (stepScale T lam m * (lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1))))) hyL))).trans ?_
    refine (push ((restrictTorus (simScale α (stepScale T lam (m + (i + 1)))) b).comp
      ((lam ^ dilExponent α / θ) ^ (i + 1) •
      fracTorusHeat α (stepScale T lam m * (lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1)))))
      (1 - lam) hL0.le hL1).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [if_neg (Nat.succ_ne_zero i), ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 - lam)] with σ hne hmem
    rw [uIoc_of_le hL0.le] at hmem
    have hτ : 0 < 1 - lam - σ := sub_pos.2 (lt_of_le_of_ne hmem.2 hne)
    have e2 : lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1) + (1 - lam - σ) =
        1 - σ - lam ^ (i + 1) * (1 - s) := by ring
    exact entry_pointwise hF hE _ _ _ hμ0 ht hτ e2 (scalar_split hl.le (i + 1)) _

end Breakdown.Periodic
