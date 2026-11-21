import Breakdown.Frac.StTorusStepCompare
import Breakdown.Torus.CompareTail

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracTorusCompareTail.Internal

open CompareTail.Internal

theorem norm_scaledDil_le {κ : ℝ} (F : ScaledMildFramework Freq.X κ) {μ : ℝ} (hμ : 0 < μ) :
    ‖F.D μ‖ ≤ μ ^ κ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hμ.le _) fun u => (F.D_norm μ hμ u).le

set_option maxHeartbeats 2000000 in
theorem norm_scaledShift_entry {κ : ℝ} (F : ScaledMildFramework Freq.X κ) (P : ℝ) (k : ℕ) {θ : ℝ}
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

end FracTorusCompareTail.Internal

open CompareTail.Internal FracTorusCompareTail.Internal in
theorem fracTailBound (α : ℝ) (hα : 1 < α) (hN : ShiftChainNorm) (hO : FracOperatorNormBounds α hα)
    (hRR : RestrictR3Bound) : FracTailBound α hα := by
  intro F _ _ _ P k θ b A hl hl1 hP hk _ hθ _ hb
  obtain ⟨C, hC0, hR3L, hTL, -, -, -, -⟩ := hO
  obtain ⟨C3, hC3, hR3⟩ := hRR
  obtain ⟨CA, hCA⟩ := A.bound
  have hMn := norm_r3Piece_le A CA hCA
  have hM0 : 0 ≤ (A.terms : ℝ) * (max CA 0 * max CA 0) := by positivity
  have hlt : Real.exp (-(P / k)) < 1 :=
    Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hP (Nat.cast_pos.2 hk)))
  have hθ0 : 0 < θ := (Real.rpow_nonneg hl.le _).trans_lt hθ
  have hc : 0 ≤ Real.exp (-(P / k)) ^ dilExponent α / θ := div_nonneg (Real.rpow_nonneg hl.le _) hθ0.le
  have hL0 : 0 < MildFramework.stepLength P k := sub_pos.2 hlt
  have hL1 : MildFramework.stepLength P k ≤ 1 := sub_le_self _ hl.le
  have hK0 : 0 ≤ max restrictTorusFun_bound.choose C3 := le_max_of_le_right hC3
  refine ⟨max restrictTorusFun_bound.choose C3 * (C * ((A.terms : ℝ) * (max CA 0 * max CA 0))),
    mul_nonneg hK0 (mul_nonneg hC0 hM0), ?_⟩
  intro T hT hT1 hsb ζ m j s
  constructor
  · have h1 := norm_chain_apply_le hN (fracTorusStep α hα T (Real.exp (-(P / k))) θ hT hT1 hl hl1) _ hc
      (fun n => by unfold fracTorusStep; exact norm_torusShift_entry _ _ _ hc)
      (restrictTorus (simScale α (stepScale T (Real.exp (-(P / k))) (m + j))) b)
      (max restrictTorusFun_bound.choose C3) ((norm_restrictTorus_le _ _).trans (le_max_left _ _))
      (fracTorusLambda α A T (Real.exp (-(P / k))) ζ m) m j s
    have hy : ‖fracTorusLambda α A T (Real.exp (-(P / k))) ζ m‖ ≤
        C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖ :=
      (lp.norm_apply_le_norm ENNReal.top_ne_zero _ m).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hTL b T _ _ A hT hT1 hl hlt hb hsb hMn) (norm_nonneg _)))
    calc _ ≤ _ := h1
      _ ≤ max restrictTorusFun_bound.choose C3 * (Real.exp (-(P / k)) ^ dilExponent α / θ) ^ j *
          (C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg hK0 (pow_nonneg hc _))
      _ = _ := by ring
  · have h1 := norm_chain_apply_le hN (fracR3Step F P k θ) _ hc
      (fun n => by unfold fracR3Step; exact norm_scaledShift_entry F P k hθ0)
      (restrictR3 b) (max restrictTorusFun_bound.choose C3) ((hR3 b).trans (le_max_right _ _))
      (fracR3Lambda α A ζ m) m j s
    have hy : ‖fracR3Lambda α A ζ m‖ ≤ C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖ :=
      (lp.norm_apply_le_norm ENNReal.top_ne_zero _ m).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hR3L _ b _ A hL0 hL1 hMn) (norm_nonneg _)))
    calc _ ≤ _ := h1
      _ ≤ max restrictTorusFun_bound.choose C3 * (Real.exp (-(P / k)) ^ dilExponent α / θ) ^ j *
          (C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg hK0 (pow_nonneg hc _))
      _ = _ := by ring

end Breakdown.Periodic
