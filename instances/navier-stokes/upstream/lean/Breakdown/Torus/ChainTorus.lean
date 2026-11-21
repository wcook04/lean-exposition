import Breakdown.Torus.StatementsInverse
import Breakdown.Torus.Forced
import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

noncomputable section

namespace Breakdown.Periodic

namespace ChainTorus.Internal

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem seqOp_eq_of (A : ℕ → E →L[ℝ] X) (T₀ : lp (fun _ : ℕ => E) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞)
    (h : ∀ g n, T₀ g n = A n (g n)) : seqOp A = T₀ := by
  have hex : ∃ T : lp (fun _ : ℕ => E) ∞ →L[ℝ] lp (fun _ : ℕ => X) ∞, ∀ g n, T g n = A n (g n) :=
    ⟨T₀, h⟩
  unfold seqOp
  rw [dif_pos hex]
  refine ContinuousLinearMap.ext fun g => lp.ext (funext fun n => ?_)
  rw [hex.choose_spec, h]

theorem extend_eq {L : ℝ} (hL : 0 ≤ L) (f : Piece X L) (σ : ℝ) :
    extendPiece f σ = f (projIcc 0 L hL σ) := by
  simp only [extendPiece, dif_pos hL]
  rfl

def weightedPiece {L : ℝ} (w : C(Icc (0 : ℝ) L, ℝ)) (x : V) : Piece V L :=
  ⟨fun s => w s • x, by fun_prop⟩

theorem torusPiece_eq_sum {L b : ℝ} (A : Approximant L b) (μ : ℝ) (n : ℕ) :
    A.torusPiece μ n = ∑ l, weightedPiece (A.weight n l)
      ((μ ^ (1 / 4 : ℝ)) • toV (transplantField μ (A.field n l))) := by
  ext s
  simp [Approximant.torusPiece, weightedPiece]

theorem lambdaTorus_eq_heat (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) {μ σ τ : ℝ}
    (hμ : 0 < μ) (hσ : 0 < σ) (h : σ ≤ τ) (ζ : ShellData) :
    lambdaTorus φ hφ b μ τ ζ = -((μ ^ (-(1 / 4 : ℝ))) • heat (μ * τ - μ * σ)
      (forceV (μ * σ) (fun x => (advectShell φ hφ b ζ : Space → Space) (simCoord μ x)))) := by
  show -((μ ^ (-(1 / 4 : ℝ))) • sourceFun μ τ (advectShell φ hφ b ζ)) = _
  rw [sourceFun, if_pos hμ,
    Forced.Internal.forceV_eq_heat (mul_pos hμ hσ) (mul_le_mul_of_nonneg_left h hμ.le)]

theorem lambdaTorus_continuousOn (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) {μ : ℝ}
    (hμ : 0 < μ) (ζ : ShellData) : ContinuousOn (fun τ => lambdaTorus φ hφ b μ τ ζ) (Ioi 0) := by
  intro τ₀ hτ₀
  have hτ₀' : (0 : ℝ) < τ₀ := hτ₀
  apply ContinuousAt.continuousWithinAt
  set x := forceV (μ * (τ₀ / 2)) (fun x => (advectShell φ hφ b ζ : Space → Space) (simCoord μ x))
  have hev : (fun τ => -((μ ^ (-(1 / 4 : ℝ))) • heat (μ * τ - μ * (τ₀ / 2)) x)) =ᶠ[𝓝 τ₀]
      (fun τ => lambdaTorus φ hφ b μ τ ζ) := by
    filter_upwards [Ici_mem_nhds (half_lt_self hτ₀')] with τ hτ
    rw [lambdaTorus_eq_heat φ hφ b hμ (half_pos hτ₀') hτ]
  refine ContinuousAt.congr ?_ hev
  have hpos : 0 < μ * τ₀ - μ * (τ₀ / 2) := by nlinarith
  have hc : ContinuousAt (fun t => heat t x) (μ * τ₀ - μ * (τ₀ / 2)) :=
    (heat_continuousOn x).continuousAt (Ici_mem_nhds hpos)
  have hl : ContinuousAt (fun τ : ℝ => μ * τ - μ * (τ₀ / 2)) τ₀ := by fun_prop
  exact ((hc.comp_of_eq hl rfl).const_smul (μ ^ (-(1 / 4 : ℝ)))).neg

theorem isShellScale_step {T lam b : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1)
    (hb : 0 < b) (hTb : Real.sqrt T * b ≤ 1 / 8) (n : ℕ) : IsShellScale (stepScale T lam n) b := by
  refine ⟨stepScale_pos hT hl n, stepScale_le_one hT1 hl hl1 n, hb, ?_⟩
  have h1 : stepScale T lam n ≤ T := mul_le_of_le_one_right hT.le (pow_le_one₀ hl.le hl1)
  exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h1) hb.le).trans hTb

set_option maxHeartbeats 2000000 in
theorem chain_apply (hF : TorusFactor) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hV : PieceConvSpec) (hP : PieceOperatorStatement) (hK : KernelSharpBound) {T lam b : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (hl : 0 < lam) (hl1 : lam ≤ 1) (A : Approximant (1 - lam) b)
    (hlt : lam < 1) (hb : 0 < b) (hTb : Real.sqrt T * b ≤ 1 / 8) (CΛ : ℝ) (hCΛ0 : 0 ≤ CΛ)
    (hCΛ : ∀ (φ : Space → Space) (hφ : IsTestField φ) (b μ τ : ℝ), IsShellScale μ b →
      0 < τ → μ * τ ≤ 1 → ∀ ζ : ShellData,
        ‖lambdaTorus φ hφ b μ τ ζ‖ ≤ CΛ * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖)
    (CA : ℝ) (hCA : ∀ n l, ‖Freq.embedX (A.field n l)‖ ≤ CA ∧ ‖A.weight n l‖ ≤ CA) :
    ∀ g n, ((torusLambda A T lam).comp (torusRestrict (1 - lam) b T lam)) g n =
      ((2 : ℝ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam)
          (A.torusPiece (stepScale T lam n) n)) (g n) := by
  have hCb0 : 0 ≤ max CA 0 := le_max_right _ _
  have hL0 : 0 < 1 - lam := by linarith
  have hL1 : 1 - lam ≤ 1 := by linarith
  have hq : 0 ≤ (1 - lam) ^ (1 / 4 : ℝ) := rpow_nonneg hL0.le _
  have hsh := isShellScale_step hT hT1 hl hl1 hb hTb
  have hC0 : 0 ≤ CΛ * max CA 0 := mul_nonneg hCΛ0 hCb0
  have hΛb : ∀ n l τ, 0 < τ → τ ≤ 1 →
      ‖lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ‖ ≤
        CΛ * max CA 0 * τ ^ (-(3 / 4 : ℝ)) := by
    intro n l τ hτ hτ1
    have hr : 0 ≤ τ ^ (-(3 / 4 : ℝ)) := rpow_nonneg hτ.le _
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 hr) fun ζ => ?_
    have h1 := hCΛ _ (A.isTest n l) b _ τ (hsh n) hτ
      (mul_le_one₀ (stepScale_le_one hT1 hl hl1 n) hτ.le hτ1) ζ
    have h2 : ‖Freq.embedX (A.field n l)‖ ≤ max CA 0 := (hCA n l).1.trans (le_max_left _ _)
    calc _ ≤ _ := h1
      _ ≤ CΛ * τ ^ (-(3 / 4 : ℝ)) * max CA 0 * ‖ζ‖ := by
          gcongr
      _ = _ := by ring
  have hPC := fun n l => hV ShellData V (1 - lam)
    (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ) (A.weight n l)
    (CΛ * max CA 0) hL0 hL1 hC0 (hΛb n l)
    (fun ζ => lambdaTorus_continuousOn _ _ _ (stepScale_pos hT hl n) ζ)
  have hBn : ∀ n, ‖∑ l, pieceConv (1 - lam)
      (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ) (A.weight n l)‖ ≤
        A.terms * (4 * (CΛ * max CA 0) * (1 - lam) ^ (1 / 4 : ℝ) * max CA 0) := by
    intro n
    calc _ ≤ ∑ l, ‖pieceConv (1 - lam)
          (fun τ => lambdaTorus (A.field n l) (A.isTest n l) b (stepScale T lam n) τ)
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
  have hRb : ∀ n, ‖pieceComp (1 - lam) (restrictTorus (stepScale T lam n) b)‖ ≤
      restrictTorusFun_bound.choose := fun n =>
    (hC _ _ _ _ hL0.le).2.trans (LinearMap.mkContinuous_norm_le _ hCr0 _)
  have hTR := (hS (Piece V (1 - lam)) (Piece ShellData (1 - lam)) _ _ hRb hCr0).1
  intro g n
  refine ContinuousMap.ext fun s => ?_
  rw [ContinuousLinearMap.comp_apply]
  unfold torusLambda torusRestrict
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
  have hpc : extendPiece (pieceComp (1 - lam) (restrictTorus (stepScale T lam n) b) (g n)) σ =
      restrictTorus (stepScale T lam n) b (extendPiece (g n) σ) := by
    rw [extend_eq hL0.le, extend_eq hL0.le, (hC _ _ _ _ hL0.le).1]
  rw [hpc, ← hF _ (A.isTest n l) b _ (hsh n) (A.support n l) _ hτ]
  show _ = (2 : ℝ) • (((stepScale T lam n) ^ (3 / 4 : ℝ)) • kernel (stepScale T lam n * ((s : ℝ) - σ)))
    (extendPiece (weightedPiece (A.weight n l)
      ((stepScale T lam n ^ (1 / 4 : ℝ)) • toV (transplantField (stepScale T lam n) (A.field n l)))) σ)
    (extendPiece (g n) σ)
  rw [extend_eq hL0.le (weightedPiece _ _), extend_eq hL0.le (A.weight n l)]
  simp only [weightedPiece, ContinuousMap.coe_mk, map_smul, smul_apply, smul_smul]
  congr 1
  ring

end ChainTorus.Internal

open ChainTorus.Internal in
theorem torusChainEq (hF : TorusFactor) (hL : TorusLambdaBound) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hV : PieceConvSpec) (hP : PieceOperatorStatement) : TorusChainEq := by
  intro hK T lam θ b hT hT1 hl hl1 E _ _ Jt A hlt hb hTb
  have key : (torusLambda A T lam).comp (torusRestrict (1 - lam) b T lam) =
      seqOp fun n => (2 : ℝ) • (stepFrame hK (stepScale T lam n) (stepScale_pos hT hl n)
        (stepScale_le_one hT1 hl hl1 n)).pieceBil (1 - lam) (A.torusPiece (stepScale T lam n) n) :=
    (seqOp_eq_of _ _ (chain_apply hF hS hC hV hP hK hT hT1 hl hl1 A hlt hb hTb hL.choose
      hL.choose_spec.1 hL.choose_spec.2 A.bound.choose A.bound.choose_spec)).symm
  simp only [chainOp, torusOp, key]

end Breakdown.Periodic
