import Breakdown.Frac.StTorusStepCompare
import Breakdown.Torus.SeqOps

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace FracCompareEntryR3.Internal

theorem lambda_apply (α : ℝ) (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ) (ζ : ShellData) :
    fracLambdaR3 α φ hφ b τ ζ = -(Freq.fracHeatSolenoidal α τ (advectShell φ hφ b ζ)) := by
  simp only [fracLambdaR3, neg_apply, ContinuousLinearMap.comp_apply]

theorem rpow_exponent_le (α : ℝ) (hα : 1 < α) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := by
  have h : 3 / (4 * α) ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  exact Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith)

theorem lambda_opNorm_le (α : ℝ) (hα : 1 < α) (hB : FracR3LambdaBound α) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → τ ≤ 1 →
      ‖fracLambdaR3 α φ hφ b τ‖ ≤ C * ‖Freq.embedX φ‖ * τ ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := hB
  refine ⟨C, hC, fun φ hφ b τ hτ hτ1 => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC (norm_nonneg _)) (Real.rpow_nonneg hτ.le _)) fun ζ => ?_
  have hr := rpow_exponent_le α hα hτ hτ1
  have hCφ : 0 ≤ C * ‖Freq.embedX φ‖ := mul_nonneg hC (norm_nonneg _)
  calc ‖fracLambdaR3 α φ hφ b τ ζ‖ ≤ C * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖ζ‖ :=
        h φ hφ b τ hτ ζ
    _ = C * ‖Freq.embedX φ‖ * τ ^ (-(3 / (4 * α))) * ‖ζ‖ := by ring
    _ ≤ C * ‖Freq.embedX φ‖ * τ ^ (-(3 / 4 : ℝ)) * ‖ζ‖ := by
        gcongr

theorem lambda_continuousOn (α : ℝ) (hC : FracHeatSolenoidalContinuous α) (φ : Space → Space)
    (hφ : IsTestField φ) (b : ℝ) (ζ : ShellData) :
    ContinuousOn (fun τ => fracLambdaR3 α φ hφ b τ ζ) (Ioi 0) := by
  simp only [lambda_apply]
  exact (hC _).neg

theorem integrand_intervalIntegrable (α : ℝ) (hα : 1 < α) (hC : FracHeatSolenoidalContinuous α)
    (hB : FracR3LambdaBound α) {L : ℝ}
    (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (w : C(Icc (0 : ℝ) L, ℝ))
    (ζ : Piece ShellData L) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    IntervalIntegrable (fun σ => extendPiece w σ • fracLambdaR3 α φ hφ b (u - σ) (extendPiece ζ σ))
      volume 0 u := by
  obtain ⟨C, hC0, hCb⟩ := lambda_opNorm_le α hα hB
  have h := SeqOps.Internal.convKernel_integrable (fun τ => fracLambdaR3 α φ hφ b τ) w
    (C := C * ‖Freq.embedX φ‖) (mul_nonneg hC0 (norm_nonneg _))
    (fun τ hτ hτ1 => hCb φ hφ b τ hτ hτ1) (lambda_continuousOn α hC φ hφ b) ζ u hu hu1
  have h2 := (h.comp_sub_left u).symm
  simp only [sub_self, sub_zero] at h2
  simp only [SeqOps.Internal.convKernel, sub_sub_cancel] at h2
  exact h2

theorem map_lambda_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (α : ℝ) (hα : 1 < α) (hC : FracHeatSolenoidalContinuous α) (hB : FracR3LambdaBound α) {L b : ℝ}
    (A : Approximant L b) (ζ : ShellSeq L) (m : ℕ) (M : Freq.X →L[ℝ] E) {u : ℝ} (hu : 0 ≤ u)
    (hu1 : u ≤ 1) :
    M (∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ •
        fracLambdaR3 α (A.field m l) (A.isTest m l) b (u - σ) (extendPiece (ζ m) σ)) =
      ∑ l, ∫ σ in (0 : ℝ)..u, extendPiece (A.weight m l) σ •
        M (fracLambdaR3 α (A.field m l) (A.isTest m l) b (u - σ) (extendPiece (ζ m) σ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm M
    (integrand_intervalIntegrable α hα hC hB _ _ b _ _ hu hu1)]
  simp only [map_smul]

theorem pieceEnd_eq {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {T : ℝ} (hT : 0 ≤ T)
    (f : Piece X T) : pieceEnd T f = f ⟨T, hT, le_rfl⟩ := by
  simp only [pieceEnd, dif_pos hT, ContinuousMap.evalCLM_apply]

theorem shiftChain_self {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (B : ℕ → X →L[ℝ] X)
    (m : ℕ) : shiftChain B m m = ContinuousLinearMap.id ℝ X := by
  cases m <;> simp [shiftChain]

set_option maxHeartbeats 400000 in
theorem succ_entry (α : ℝ) (hα : 1 < α) (hCh : FracR3ChainFormula α) (hS : FracHeatSolenoidalShift α)
    (hC : FracHeatSolenoidalContinuous α) (hB : FracR3LambdaBound α)
    (F : ScaledMildFramework Freq.X (dilExponent α)) (hG : F.G = Freq.fracHeatX α)
    (hD : F.D = Freq.fracDilX α)
    (P : ℝ) (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b) (hP : 0 < P)
    (hk : 0 < k) (hL0 : 0 < MildFramework.stepLength P k) (hL1 : MildFramework.stepLength P k ≤ 1)
    (ζ : ShellSeq (MildFramework.stepLength P k)) (m i : ℕ)
    (s : Icc (0 : ℝ) (MildFramework.stepLength P k)) (y : Piece Freq.X (MildFramework.stepLength P k))
    (hy : y ⟨MildFramework.stepLength P k, hL0.le, le_rfl⟩ =
        ∑ l, ∫ σ in (0 : ℝ)..MildFramework.stepLength P k, extendPiece (A.weight m l) σ •
          fracLambdaR3 α (A.field m l) (A.isTest m l) b (MildFramework.stepLength P k - σ)
            (extendPiece (ζ m) σ)) :
    restrictR3 b (shiftChain (fracR3Step F P k θ) m (m + i + 1) y s) = (θ⁻¹) ^ (i + 1) • ∑ l,
        ∫ σ in (0 : ℝ)..MildFramework.stepLength P k,
          extendPiece (A.weight m l) σ • restrictR3 b (Freq.fracDilX α (Real.exp (-(P / k)) ^ (i + 1))
            (-(Freq.fracHeatSolenoidal α (1 - σ - Real.exp (-(P / k)) ^ (i + 1) * (1 - s))
              (advectShell (A.field m l) (A.isTest m l) b (extendPiece (ζ m) σ))))) := by
  have hlam0 : 0 < Real.exp (-(P / k)) := Real.exp_pos _
  have hlam1 : Real.exp (-(P / k)) ≤ 1 := by
    have : 0 < MildFramework.stepLength P k := hL0
    simp only [MildFramework.stepLength] at this
    linarith
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have ht0 : 0 ≤ Real.exp (-(P / k)) ^ (i + 1) * s + Real.exp (-(P / k)) -
      Real.exp (-(P / k)) ^ (i + 1) := by
    have h1 : Real.exp (-(P / k)) ^ (i + 1) ≤ Real.exp (-(P / k)) :=
      pow_le_of_le_one hlam0.le hlam1 (Nat.succ_ne_zero i)
    have h2 : 0 ≤ Real.exp (-(P / k)) ^ (i + 1) * s := mul_nonneg (pow_nonneg hlam0.le _) hs0
    linarith
  have heq : ∀ σ : ℝ, Real.exp (-(P / k)) ^ (i + 1) * s + Real.exp (-(P / k)) -
      Real.exp (-(P / k)) ^ (i + 1) + (MildFramework.stepLength P k - σ) =
        1 - σ - Real.exp (-(P / k)) ^ (i + 1) * (1 - s) := by
    intro σ
    simp only [MildFramework.stepLength]
    ring
  rw [hCh F hG hD P k θ hP hk y m i s, (restrictR3 b).map_smul, pieceEnd_eq hL0.le, hy]
  refine congrArg (fun v => (θ⁻¹) ^ (i + 1) • v) ?_
  rw [show ∀ x, restrictR3 b (Freq.fracDilX α (Real.exp (-(P / k)) ^ (i + 1))
      (Freq.fracHeatX α (Real.exp (-(P / k)) ^ (i + 1) * s + Real.exp (-(P / k)) -
        Real.exp (-(P / k)) ^ (i + 1)) x)) =
      ((restrictR3 b).comp ((Freq.fracDilX α (Real.exp (-(P / k)) ^ (i + 1))).comp
        (Freq.fracHeatX α (Real.exp (-(P / k)) ^ (i + 1) * s + Real.exp (-(P / k)) -
          Real.exp (-(P / k)) ^ (i + 1))))) x from fun _ => rfl,
    map_lambda_sum α hα hC hB A ζ m _ hL0.le hL1]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ MildFramework.stepLength P k := by
    rw [ae_iff]
    simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hne] with σ hσL hσ
  rw [Set.uIoc_of_le hL0.le] at hσ
  have hσ2 : σ < MildFramework.stepLength P k := lt_of_le_of_ne hσ.2 hσL
  have e1 : Freq.fracHeatX α (Real.exp (-(P / k)) ^ (i + 1) * s + Real.exp (-(P / k)) -
      Real.exp (-(P / k)) ^ (i + 1)) (fracLambdaR3 α (A.field m l) (A.isTest m l) b
        (MildFramework.stepLength P k - σ) (extendPiece (ζ m) σ)) =
      -(Freq.fracHeatSolenoidal α (1 - σ - Real.exp (-(P / k)) ^ (i + 1) * (1 - s))
        (advectShell (A.field m l) (A.isTest m l) b (extendPiece (ζ m) σ))) := by
    rw [lambda_apply, ContinuousLinearMap.map_neg, hS _ _ ht0 (sub_pos.2 hσ2), heq]
  exact congrArg (fun v => extendPiece (A.weight m l) σ • restrictR3 b
    (Freq.fracDilX α (Real.exp (-(P / k)) ^ (i + 1)) v)) e1

end FracCompareEntryR3.Internal

set_option maxHeartbeats 400000 in
open FracCompareEntryR3.Internal in
theorem fracR3EntryFormula (α : ℝ) (hα : 1 < α) (hCh : FracR3ChainFormula α)
    (hL : FracR3LambdaFormula α) (hS : FracHeatSolenoidalShift α) (hC : FracHeatSolenoidalContinuous α)
    (hB : FracR3LambdaBound α) : FracR3EntryFormula α := by
  intro F _hK hG hD P k θ b A hP hk hL2 _hθ _hb ζ m j s
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hlam1 : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hP hk'))
  have hL0 : 0 < MildFramework.stepLength P k := by
    show 0 < 1 - Real.exp (-(P / k))
    linarith
  have hL1 : MildFramework.stepLength P k ≤ 1 := by linarith
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2.trans hL1
  rcases j with _ | i
  · have hD1 : Freq.fracDilX α 1 = ContinuousLinearMap.id ℝ Freq.X := hD ▸ F.D_one
    rw [Nat.add_zero, fracR3Entry, shiftChain_self]
    simp only [pow_zero, one_smul, one_mul, ↓reduceIte]
    rw [ContinuousLinearMap.id_apply, hL _ b A hL0 hL1 ζ m s,
      map_lambda_sum α hα hC hB A ζ m (restrictR3 b) hs0 hs1]
    refine Finset.sum_congr rfl fun l _ => intervalIntegral.integral_congr fun σ _ => ?_
    simp only [hD1, ContinuousLinearMap.id_apply, lambda_apply]
    rw [show (1 : ℝ) - σ - (1 - s) = s - σ by ring]
  · show restrictR3 b (shiftChain (fracR3Step F P k θ) m (m + i + 1) (fracR3Lambda α A ζ m) s) = _
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    exact succ_entry α hα hCh hS hC hB F hG hD P k θ b A hP hk hL0 hL1 ζ m i s _
      (hL _ b A hL0 hL1 ζ m _)

end Breakdown.Periodic
