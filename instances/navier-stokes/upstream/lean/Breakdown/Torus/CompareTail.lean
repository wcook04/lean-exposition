import Breakdown.Torus.CompareStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CompareTail.Internal

theorem norm_pieceFree_le {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (H : HeatBilinear Y) (T : ℝ) : ‖H.pieceFree T‖ ≤ 1 := by
  unfold HeatBilinear.pieceFree
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg x)).2 fun t => ?_
    rw [h.choose_spec x t]
    simpa using (H.G t).le_of_opNorm_le (H.G_norm t t.2.1) x
  · simp

theorem norm_pieceEnd_le {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : ℝ) :
    ‖(pieceEnd T : Piece Y T →L[ℝ] Y)‖ ≤ 1 := by
  unfold pieceEnd
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem norm_dil_le (F : MildFramework Freq.X) {μ : ℝ} (hμ : 0 < μ) : ‖F.D μ‖ ≤ μ ^ (1 / 4 : ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hμ.le _) fun u => (F.D_norm μ hμ u).le

set_option maxHeartbeats 2000000 in
theorem norm_r3Shift_entry (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ‖θ⁻¹ • (F.stepFree P k).comp (F.stepEnd P k)‖ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ := by
  have h1 : ‖F.stepFree P k‖ ≤ 1 := norm_pieceFree_le F.toHeatBilinear _
  have h2 : ‖F.stepEnd P k‖ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) := by
    show ‖(F.D (Real.exp (-(P / k)))).comp (pieceEnd (MildFramework.stepLength P k))‖ ≤ _
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc _ ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) * 1 :=
          mul_le_mul (norm_dil_le F (Real.exp_pos _)) (norm_pieceEnd_le _) (norm_nonneg _)
            (Real.rpow_nonneg (Real.exp_pos _).le _)
      _ = _ := mul_one _
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hθ.le, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hθ.le)
  calc _ ≤ ‖F.stepFree P k‖ * ‖F.stepEnd P k‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * Real.exp (-(P / k)) ^ (1 / 4 : ℝ) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_torusShift_entry (H : HeatBilinear V) (L c : ℝ) (hc : 0 ≤ c) :
    ‖c • (H.pieceFree L).comp (pieceEnd L)‖ ≤ c := by
  rw [norm_smul, Real.norm_of_nonneg hc]
  calc c * ‖(H.pieceFree L).comp (pieceEnd L)‖ ≤ c * (‖H.pieceFree L‖ * ‖(pieceEnd L : Piece V L →L[ℝ] V)‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hc
    _ ≤ c * (1 * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul (norm_pieceFree_le H L) (norm_pieceEnd_le L) (norm_nonneg _) zero_le_one) hc
    _ = c := by ring

theorem norm_r3Piece_le {L b : ℝ} (A : Approximant L b) (C : ℝ)
    (hC : ∀ n l, ‖Freq.embedX (A.field n l)‖ ≤ C ∧ ‖A.weight n l‖ ≤ C) (n : ℕ) :
    ‖A.r3Piece n‖ ≤ (A.terms : ℝ) * (max C 0 * max C 0) := by
  have h0 : 0 ≤ (A.terms : ℝ) * (max C 0 * max C 0) := by positivity
  refine (ContinuousMap.norm_le _ h0).2 fun s => ?_
  show ‖∑ l, A.weight n l s • Freq.embedX (A.field n l)‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  have hl : ∀ l ∈ (Finset.univ : Finset (Fin A.terms)),
      ‖A.weight n l s • Freq.embedX (A.field n l)‖ ≤ max C 0 * max C 0 := by
    intro l _
    rw [norm_smul]
    exact mul_le_mul (((A.weight n l).norm_coe_le_norm s).trans ((hC n l).2.trans (le_max_left _ _)))
      ((hC n l).1.trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  refine (Finset.sum_le_sum hl).trans (le_of_eq ?_)
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem norm_restrictTorus_le (μ b : ℝ) : ‖restrictTorus μ b‖ ≤ restrictTorusFun_bound.choose :=
  LinearMap.mkContinuous_norm_le _ restrictTorusFun_bound.choose_spec.1 _

theorem norm_chain_apply_le (hN : ShiftChainNorm) {L : ℝ} {X Y : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (B : ℕ → Piece X L →L[ℝ] Piece X L) (c : ℝ) (hc : 0 ≤ c) (hB : ∀ n, ‖B n‖ ≤ c)
    (R : X →L[ℝ] Y) (CR : ℝ) (hR : ‖R‖ ≤ CR) (y : Piece X L) (m j : ℕ) (s : Icc (0 : ℝ) L) :
    ‖R (shiftChain B m (m + j) y s)‖ ≤ CR * c ^ j * ‖y‖ := by
  have h1 := hN (Piece X L) B c hc hB m (m + j) (Nat.le_add_right m j)
  rw [Nat.add_sub_cancel_left] at h1
  calc ‖R (shiftChain B m (m + j) y s)‖ ≤ ‖R‖ * ‖shiftChain B m (m + j) y s‖ := R.le_opNorm _
    _ ≤ CR * (c ^ j * ‖y‖) := by
      refine mul_le_mul hR ?_ (norm_nonneg _) ((norm_nonneg _).trans hR)
      exact (ContinuousMap.norm_coe_le_norm _ s).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
    _ = CR * c ^ j * ‖y‖ := by ring

end CompareTail.Internal

open CompareTail.Internal in
theorem tailBound (hN : ShiftChainNorm) (hO : OperatorNormBounds) (hRR : RestrictR3Bound) :
    TailBound := by
  intro hK F _ _ _ P k θ b A hl hl1 hP hk _ hθ _ hb
  obtain ⟨C, hC0, hR3L, hTL, -, -, -, -⟩ := hO
  obtain ⟨C3, hC3, hR3⟩ := hRR
  obtain ⟨CA, hCA⟩ := A.bound
  have hMn := norm_r3Piece_le A CA hCA
  have hM0 : 0 ≤ (A.terms : ℝ) * (max CA 0 * max CA 0) := by positivity
  have hC4 : 0 ≤ restrictTorusFun_bound.choose := restrictTorusFun_bound.choose_spec.1
  have hlt : Real.exp (-(P / k)) < 1 :=
    Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hP (Nat.cast_pos.2 hk)))
  have hθ0 : 0 < θ := (Real.rpow_nonneg hl.le _).trans_lt hθ
  have hc : 0 ≤ Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ := div_nonneg (Real.rpow_nonneg hl.le _) hθ0.le
  have hL0 : 0 < MildFramework.stepLength P k := sub_pos.2 hlt
  have hL1 : MildFramework.stepLength P k ≤ 1 := sub_le_self _ hl.le
  have hK0 : 0 ≤ max restrictTorusFun_bound.choose C3 := le_max_of_le_right hC3
  refine ⟨max restrictTorusFun_bound.choose C3 * (C * ((A.terms : ℝ) * (max CA 0 * max CA 0))),
    mul_nonneg hK0 (mul_nonneg hC0 hM0), ?_⟩
  intro T hT hT1 hsb ζ m j s
  constructor
  · have h1 := norm_chain_apply_le hN (torusStep hK T (Real.exp (-(P / k))) θ hT hT1 hl hl1) _ hc
      (fun n => by unfold torusStep; exact norm_torusShift_entry _ _ _ hc)
      (restrictTorus (stepScale T (Real.exp (-(P / k))) (m + j)) b) (max restrictTorusFun_bound.choose C3)
      ((norm_restrictTorus_le _ _).trans (le_max_left _ _))
      (torusLambda A T (Real.exp (-(P / k))) ζ m) m j s
    have hy : ‖torusLambda A T (Real.exp (-(P / k))) ζ m‖ ≤
        C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖ :=
      (lp.norm_apply_le_norm ENNReal.top_ne_zero _ m).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hTL b T _ _ A hT hT1 hl hlt hb hsb hMn) (norm_nonneg _)))
    calc _ ≤ _ := h1
      _ ≤ max restrictTorusFun_bound.choose C3 * (Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ) ^ j *
          (C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg hK0 (pow_nonneg hc _))
      _ = _ := by ring
  · have h1 := norm_chain_apply_le hN (r3Step F P k θ) _ hc
      (fun n => by unfold r3Step; exact norm_r3Shift_entry F P k hθ0)
      (restrictR3 b) (max restrictTorusFun_bound.choose C3) ((hR3 b).trans (le_max_right _ _)) (r3Lambda A ζ m) m j s
    have hy : ‖r3Lambda A ζ m‖ ≤ C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖ :=
      (lp.norm_apply_le_norm ENNReal.top_ne_zero _ m).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hR3L _ b _ A hL0 hL1 hMn) (norm_nonneg _)))
    calc _ ≤ _ := h1
      _ ≤ max restrictTorusFun_bound.choose C3 * (Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ) ^ j *
          (C * ((A.terms : ℝ) * (max CA 0 * max CA 0)) * ‖ζ‖) :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg hK0 (pow_nonneg hc _))
      _ = _ := by ring

end Breakdown.Periodic
