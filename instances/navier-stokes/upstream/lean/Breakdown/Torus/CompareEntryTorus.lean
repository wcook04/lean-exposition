import Breakdown.Torus.CompareStatements
import Breakdown.Torus.ChainTorus
import Breakdown.Torus.SeqOps
import Breakdown.Torus.ShellTorusBase

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace CompareEntryTorus.Internal

theorem shiftChain_self {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (B : ℕ → X →L[ℝ] X)
    (m : ℕ) : shiftChain B m m = ContinuousLinearMap.id ℝ X := by
  cases m with
  | zero => simp [shiftChain]
  | succ n => simp [shiftChain]

theorem lambda_integrable (hB : TorusLambdaBound) {L b : ℝ} (A : Approximant L b) {μ : ℝ}
    (hμ : IsShellScale μ b) (n : ℕ) (l : Fin A.terms) (ζ : Piece ShellData L) {u : ℝ} (hu : 0 ≤ u)
    (hu1 : u ≤ 1) :
    IntervalIntegrable (fun σ => extendPiece (A.weight n l) σ •
      lambdaTorus (A.field n l) (A.isTest n l) b μ (u - σ) (extendPiece ζ σ)) volume 0 u := by
  obtain ⟨C, hC0, hC⟩ := hB
  have hK0 : 0 ≤ C * ‖Freq.embedX (A.field n l)‖ := mul_nonneg hC0 (norm_nonneg _)
  have hΛ : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ‖lambdaTorus (A.field n l) (A.isTest n l) b μ τ‖ ≤
      (C * ‖Freq.embedX (A.field n l)‖) * τ ^ (-(3 / 4 : ℝ)) := by
    intro τ hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK0 (rpow_nonneg hτ.le _)) fun ζ => ?_
    calc _ ≤ _ := hC _ (A.isTest n l) b μ τ hμ hτ (mul_le_one₀ hμ.2.1 hτ.le hτ1) ζ
      _ = _ := by ring
  have h := SeqOps.Internal.convKernel_integrable
    (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b μ τ) (A.weight n l) hK0 hΛ
    (fun ζ => ChainTorus.Internal.lambdaTorus_continuousOn _ _ _ hμ.1 ζ) ζ u hu hu1
  have h2 := (h.comp_sub_left u).symm
  simp only [sub_zero, sub_self] at h2
  simpa only [SeqOps.Internal.convKernel, sub_sub_cancel] using h2

open ShellTorus.Internal in
theorem heat_lambdaTorus (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) {μ t τ : ℝ} (hμ : 0 < μ)
    (ht : 0 ≤ t) (hτ : 0 < τ) (ζ : ShellData) :
    heat (μ * t) (lambdaTorus φ hφ b μ τ ζ) = lambdaTorus φ hφ b μ (t + τ) ζ := by
  rw [ChainTorus.Internal.lambdaTorus_eq_heat φ hφ b hμ hτ (by linarith : τ ≤ t + τ),
    lambdaTorus_apply, sourceOp_apply hμ, map_neg, map_smul,
    show μ * (t + τ) - μ * τ = μ * t by ring]

theorem scalar_split {lam θ : ℝ} (hl : 0 ≤ lam) (n : ℕ) :
    (lam ^ (1 / 4 : ℝ) / θ) ^ n = (θ⁻¹) ^ n * (lam ^ n) ^ (1 / 4 : ℝ) := by
  rw [div_eq_mul_inv, mul_pow, rpow_pow_comm hl, mul_comm]

open ShellTorus.Internal in
theorem entry_pointwise (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) {μ μ' c d θ' w t τ τ' : ℝ}
    (hμ : 0 < μ) (ht : 0 ≤ t) (hτ : 0 < τ) (hτ' : t + τ = τ') (hc : c = θ' * d) (ζ : ShellData) :
    w • ((restrictTorus μ' b).comp (c • heat (μ * t))) (lambdaTorus φ hφ b μ τ ζ) =
      θ' • (w • restrictTorus μ' b (d • -((μ ^ (-(1 / 4 : ℝ))) •
        sourceOp μ τ' (advectShell φ hφ b ζ)))) := by
  show w • restrictTorus μ' b (c • heat (μ * t) (lambdaTorus φ hφ b μ τ ζ)) = _
  rw [heat_lambdaTorus φ hφ b hμ ht hτ, hτ', hc, map_smul, map_smul, smul_smul, smul_smul, smul_smul,
    lambdaTorus_apply]
  congr 1
  ring

theorem pieceEnd_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {L : ℝ} (h : 0 ≤ L)
    (f : Piece X L) : pieceEnd L f = f ⟨L, h, le_rfl⟩ := by
  simp only [pieceEnd, dif_pos h]
  rfl

end CompareEntryTorus.Internal

open CompareEntryTorus.Internal ChainTorus.Internal ShellTorus.Internal in
theorem torusEntryFormula (hCh : TorusChainFormula) (hL : TorusLambdaFormula) (hB : TorusLambdaBound) :
    TorusEntryFormula := by
  intro hK T lam θ hT hT1 hl hl1 b A hlt hl2 hθ hb hTb ζ m j s
  have hL0 : 0 < 1 - lam := by linarith
  have hL1 : 1 - lam ≤ 1 := by linarith
  have hsh : IsShellScale (stepScale T lam m) b := isShellScale_step hT hT1 hl hl1 hb hTb m
  have hy := hL (1 - lam) b T lam A hL0 hL1 hT hT1 hl hl1 hb hTb ζ m
  have push : ∀ (Φ : V →L[ℝ] ShellData) (u : ℝ), 0 ≤ u → u ≤ 1 →
      Φ (∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ •
        lambdaTorus (A.field m l) (A.isTest m l) b (stepScale T lam m) (u - σ) (extendPiece (ζ m) σ)) =
      ∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ •
        Φ (lambdaTorus (A.field m l) (A.isTest m l) b (stepScale T lam m) (u - σ)
          (extendPiece (ζ m) σ)) := by
    intro Φ u hu hu1
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Φ (lambda_integrable hB A hsh m l (ζ m) hu hu1)]
    simp only [map_smul]
  have hyU : ∀ (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1 - lam),
      pieceEnd (1 - lam) (torusLambda A T lam ζ m) = torusLambda A T lam ζ m ⟨u, hu, hu1⟩ →
      pieceEnd (1 - lam) (torusLambda A T lam ζ m) = ∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ •
        lambdaTorus (A.field m l) (A.isTest m l) b (stepScale T lam m) (u - σ) (extendPiece (ζ m) σ) :=
    fun u hu hu1 h => h.trans (hy ⟨u, hu, hu1⟩)
  have hyL := hyU (1 - lam) hL0.le le_rfl (pieceEnd_eq hL0.le _)
  have e1 : ∀ i : ℕ, shiftChain (torusStep hK T lam θ hT hT1 hl hl1) m (m + (i + 1))
      (torusLambda A T lam ζ m) s =
      ((lam ^ (1 / 4 : ℝ) / θ) ^ (i + 1) •
        heat (stepScale T lam m * (lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1))))
        (pieceEnd (1 - lam) (torusLambda A T lam ζ m)) :=
    fun i => hCh hK T lam θ hT hT1 hl hl1 hlt (torusLambda A T lam ζ m) m i s
  rw [Finset.smul_sum]
  unfold torusEntry
  rcases j with _ | i
  · refine (congrArg (restrictTorus (stepScale T lam m) b)
      ((congrArg (fun f : Piece V (1 - lam) →L[ℝ] Piece V (1 - lam) => f (torusLambda A T lam ζ m) s)
        (shiftChain_self (torusStep hK T lam θ hT hT1 hl hl1) m)).trans (hy s))).trans ?_
    refine (push _ s s.2.1 (s.2.2.trans hL1)).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pow_zero (θ⁻¹), one_smul, if_pos rfl]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only []
    have e : (1 : ℝ) - σ - 1 * (1 - (s : ℝ)) = s - σ := by ring
    simp only [pow_zero lam, one_rpow, one_smul]
    simp only [e]
    rfl
  · have ht : 0 ≤ lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1) := by
      have h1 : lam ^ (i + 1) ≤ lam := pow_le_of_le_one hl.le hl1 (Nat.succ_ne_zero i)
      have h2 : 0 ≤ lam ^ (i + 1) * (s : ℝ) := mul_nonneg (pow_nonneg hl.le _) s.2.1
      linarith
    refine (congrArg (restrictTorus (stepScale T lam (m + (i + 1))) b) ((e1 i).trans
      (congrArg (⇑((lam ^ (1 / 4 : ℝ) / θ) ^ (i + 1) •
        heat (stepScale T lam m * (lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1))))) hyL))).trans ?_
    refine (push ((restrictTorus (stepScale T lam (m + (i + 1))) b).comp ((lam ^ (1 / 4 : ℝ) / θ) ^ (i + 1) •
      heat (stepScale T lam m * (lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1))))) (1 - lam) hL0.le hL1).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [if_neg (Nat.succ_ne_zero i), ← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 - lam)] with σ hne hmem
    rw [uIoc_of_le hL0.le] at hmem
    have hτ : 0 < 1 - lam - σ := sub_pos.2 (lt_of_le_of_ne hmem.2 hne)
    have e2 : lam ^ (i + 1) * (s : ℝ) + lam - lam ^ (i + 1) + (1 - lam - σ) =
        1 - σ - lam ^ (i + 1) * (1 - s) := by ring
    exact entry_pointwise _ _ _ hsh.1 ht hτ e2 (scalar_split hl.le (i + 1)) _

end Breakdown.Periodic
