import Breakdown.Torus.CompareStatements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CompareLambdaAssembly.Internal

theorem pieceFree_norm_le {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (H : HeatBilinear Y) (L : ℝ) : ‖H.pieceFree L‖ ≤ 1 := by
  unfold HeatBilinear.pieceFree
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
    rw [h.choose_spec x t, one_mul]
    exact ((H.G t).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) (H.G_norm t t.2.1))
  · simp

theorem pieceEnd_norm_le {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : ℝ) :
    ‖(pieceEnd L : Piece Y L →L[ℝ] Y)‖ ≤ 1 := by
  unfold pieceEnd
  split_ifs with h
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul]
    exact ContinuousMap.norm_coe_le_norm f _
  · simp

theorem scaled_step_norm_le (H : HeatBilinear V) (L c : ℝ) (hc : 0 ≤ c) :
    ‖c • (H.pieceFree L).comp (pieceEnd L)‖ ≤ c := by
  rw [norm_smul, Real.norm_of_nonneg hc]
  refine mul_le_of_le_one_right hc ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
  exact mul_le_one₀ (pieceFree_norm_le H L) (norm_nonneg _) (pieceEnd_norm_le L)

theorem torus_apply (hN : InvSeriesEntry) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hO : OperatorNormBounds) (hK : KernelSharpBound) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam ≤ 1) (b : ℝ) (A : Approximant (1 - lam) b) (hθ : 0 < θ)
    (hq : lam ^ (1 / 4 : ℝ) / θ < 1) (hL : 0 ≤ 1 - lam) (ζ : ShellSeq (1 - lam)) (n : ℕ)
    (s : Icc (0 : ℝ) (1 - lam)) :
    ((torusRestrict (1 - lam) b T lam).comp
      ((Ring.inverse (1 - torusShift hK T lam θ hT hT1 hl hl1)).comp (torusLambda A T lam)) ζ) n s =
      ∑ m ∈ Finset.range (n + 1), torusEntry hK T lam θ hT hT1 hl hl1 b A ζ m n s := by
  obtain ⟨C, hC0, -, -, -, -, -, h6⟩ := hO
  have hq0 : 0 ≤ lam ^ (1 / 4 : ℝ) / θ := div_nonneg (Real.rpow_nonneg hl.le _) hθ.le
  have hB : ∀ n, ‖torusStep hK T lam θ hT hT1 hl hl1 n‖ ≤ lam ^ (1 / 4 : ℝ) / θ := fun n =>
    scaled_step_norm_le _ _ _ hq0
  have hshift := ((hS (Piece V (1 - lam)) (Piece V (1 - lam)) (fun _ => 0) (lam ^ (1 / 4 : ℝ) / θ)
    (fun _ => by simpa using hq0) hq0).2.2.1 _ hB).1
  have hnorm : ‖seqShift (torusStep hK T lam θ hT hT1 hl hl1)‖ < 1 :=
    (h6 hK T lam θ hT hT1 hl hl1 hθ).trans_lt hq
  have hinv := hN (Piece V (1 - lam)) (torusStep hK T lam θ hT hT1 hl hl1) hnorm hshift
  have hR0 := restrictTorusFun_bound.choose_spec.1
  have hR : ∀ μ, ‖pieceComp (1 - lam) (restrictTorus μ b)‖ ≤ restrictTorusFun_bound.choose :=
    fun μ => (hC _ _ (1 - lam) (restrictTorus μ b) hL).2.trans (LinearMap.mkContinuous_norm_le _ hR0 _)
  have hRf := (hS (Piece V (1 - lam)) (Piece ShellData (1 - lam))
    (fun n => pieceComp (1 - lam) (restrictTorus (stepScale T lam n) b)) _ (fun n => hR _) hR0).1
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  unfold torusRestrict
  rw [hRf, (hC _ _ _ _ hL).1]
  change restrictTorus _ b
    ((Ring.inverse (1 - seqShift (torusStep hK T lam θ hT hT1 hl hl1)) (torusLambda A T lam ζ)) n s) = _
  rw [hinv, ContinuousMap.coe_sum, Finset.sum_apply, map_sum]
  rfl

theorem r3_apply (hN : InvSeriesEntry) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hO : OperatorNormBounds) (F : MildFramework Freq.X) (P : ℝ) (k : ℕ) (θ b : ℝ)
    (A : Approximant (MildFramework.stepLength P k) b) (hP : 0 < P) (hk : 0 < k) (hθ : 0 < θ)
    (hq : Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ < 1) (hL : 0 ≤ MildFramework.stepLength P k)
    (ζ : ShellSeq (MildFramework.stepLength P k)) (n : ℕ)
    (s : Icc (0 : ℝ) (MildFramework.stepLength P k)) :
    ((r3Restrict _ b).comp ((Ring.inverse (1 - r3Shift F P k θ)).comp (r3Lambda A)) ζ) n s =
      ∑ m ∈ Finset.range (n + 1), r3Entry F P k θ b A ζ m n s := by
  obtain ⟨C, hC0, -, -, -, -, h5, -⟩ := hO
  have hq0 : 0 ≤ ‖r3Step F P k θ 0‖ := norm_nonneg _
  have hB : ∀ n, ‖r3Step F P k θ n‖ ≤ ‖r3Step F P k θ 0‖ := fun _ => le_rfl
  have hshift := ((hS (Piece Freq.X (MildFramework.stepLength P k))
    (Piece Freq.X (MildFramework.stepLength P k)) (fun _ => 0) _
    (fun _ => by simp) hq0).2.2.1 _ hB).1
  have hnorm : ‖seqShift (r3Step F P k θ)‖ < 1 := (h5 F P k θ hP hk hθ).trans_lt hq
  have hinv := hN (Piece Freq.X (MildFramework.stepLength P k)) (r3Step F P k θ) hnorm hshift
  have hR : ∀ _n : ℕ, ‖pieceComp (MildFramework.stepLength P k) (restrictR3 b)‖ ≤ ‖restrictR3 b‖ :=
    fun _ => (hC _ _ _ (restrictR3 b) hL).2
  have hRf := (hS (Piece Freq.X (MildFramework.stepLength P k))
    (Piece ShellData (MildFramework.stepLength P k))
    (fun _ => pieceComp (MildFramework.stepLength P k) (restrictR3 b)) _ hR (norm_nonneg _)).1
  have e1 : ∀ g : R3Seq (MildFramework.stepLength P k), (r3Restrict _ b g) n s = restrictR3 b (g n s) :=
    fun g => by unfold r3Restrict; rw [hRf, (hC _ _ _ _ hL).1]
  refine (e1 ((Ring.inverse (1 - seqShift (r3Step F P k θ))) (r3Lambda A ζ))).trans ?_
  rw [hinv]
  refine (congrArg (restrictR3 b) (ContinuousMap.sum_apply _ _ s)).trans ?_
  refine (map_sum (restrictR3 b) _ _).trans ?_
  exact Finset.sum_congr rfl fun m _ => rfl


theorem geometric_choice (q δ K : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ) (hK0 : 0 ≤ K) :
    ∃ (r c : ℝ) (N : ℕ), 0 < r ∧ r < 1 ∧ 0 < c ∧ (∀ j : ℕ, q ^ j = r ^ j * r ^ j) ∧
      2 * K * r ^ (N + 1) ≤ c ∧ c * (1 / (1 - r)) = δ / 2 := by
  have hr0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hr1 : Real.sqrt q < 1 := (Real.sqrt_lt_sqrt hq0.le hq1).trans_eq Real.sqrt_one
  have hr1' : 0 < 1 - Real.sqrt q := by linarith
  have hc : 0 < δ * (1 - Real.sqrt q) / 2 := div_pos (mul_pos hδ hr1') two_pos
  have hK1 : (0 : ℝ) < 2 * K + 1 := by linarith
  obtain ⟨N, hNr⟩ := exists_pow_lt_of_lt_one (div_pos hc hK1) hr1
  refine ⟨Real.sqrt q, δ * (1 - Real.sqrt q) / 2, N, hr0, hr1, hc, fun j => ?_, ?_, ?_⟩
  · rw [← mul_pow, Real.mul_self_sqrt hq0.le]
  · have h1 : Real.sqrt q ^ (N + 1) ≤ Real.sqrt q ^ N :=
      pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ N)
    have h2 : Real.sqrt q ^ N * (2 * K + 1) < δ * (1 - Real.sqrt q) / 2 := (lt_div_iff₀ hK1).1 hNr
    have h3 : 0 ≤ Real.sqrt q ^ (N + 1) := pow_nonneg hr0.le _
    nlinarith
  · field_simp

theorem sub_entry {L : ℝ} (f g : ShellSeq L →L[ℝ] ShellSeq L) (ζ : ShellSeq L) (n : ℕ)
    (s : Icc (0 : ℝ) L) : ((f - g) ζ) n s = (f ζ) n s - (g ζ) n s := rfl

theorem opNorm_le_of_entries {L : ℝ} (D : ShellSeq L →L[ℝ] ShellSeq L)
    (e : ShellSeq L → ℕ → ℕ → Icc (0 : ℝ) L → ShellData) (r c δ : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hc : 0 < c) (hδ : 0 < δ) (hcr : c * (1 / (1 - r)) = δ / 2)
    (hD : ∀ ζ n s, (D ζ) n s = ∑ m ∈ Finset.range (n + 1), e ζ m n s)
    (he : ∀ ζ m j s, ‖e ζ m (m + j) s‖ ≤ c * r ^ j * ‖ζ‖) : ‖D‖ ≤ δ := by
  have hr1' : 0 < 1 - r := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ hδ.le fun ζ => ?_
  refine lp.norm_le_of_forall_le (by positivity) fun n => ?_
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun s => ?_
  rw [hD]
  have hgeo : ∑ j ∈ Finset.range (n + 1), r ^ j ≤ 1 / (1 - r) := by
    rw [Finset.range_eq_Ico]
    simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := n + 1) hr0.le hr1
  calc _ ≤ ∑ m ∈ Finset.range (n + 1), c * r ^ (n - m) * ‖ζ‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
        have := he ζ m (n - m) s
        rwa [Nat.add_sub_cancel' hmn] at this
    _ = c * ‖ζ‖ * ∑ j ∈ Finset.range (n + 1), r ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Nat.add_sub_cancel, Nat.sub_sub_self (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))]
        ring
    _ ≤ c * ‖ζ‖ * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = δ / 2 * ‖ζ‖ := by rw [mul_right_comm, hcr]
    _ ≤ δ * ‖ζ‖ := by nlinarith [norm_nonneg ζ]

theorem tail_term (a b : ShellData) (K q r c z : ℝ) (j N : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hK0 : 0 ≤ K) (hz : 0 ≤ z) (hq : q ^ j = r ^ j * r ^ j)
    (hKr : 2 * K * r ^ (N + 1) ≤ c) (hj : N < j) (ha : ‖a‖ ≤ K * q ^ j * z)
    (hb : ‖b‖ ≤ K * q ^ j * z) : ‖a - b‖ ≤ c * r ^ j * z := by
  have h3 : 2 * K * r ^ j ≤ c :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 hj) (mul_nonneg zero_le_two hK0)) hKr
  calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    _ ≤ K * q ^ j * z + K * q ^ j * z := add_le_add ha hb
    _ = 2 * K * r ^ j * r ^ j * z := by rw [hq]; ring
    _ ≤ c * r ^ j * z := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h3 (pow_nonneg hr0 _)) hz

theorem window_term (a b : ShellData) (r c z : ℝ) (j N : ℕ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hc : 0 ≤ c) (hz : 0 ≤ z) (hj : j ≤ N)
    (ha : ‖a - b‖ ≤ c * r ^ N * z) : ‖a - b‖ ≤ c * r ^ j * z :=
  ha.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 hj) hc) hz)

end CompareLambdaAssembly.Internal


open CompareLambdaAssembly.Internal in
theorem lambdaComparison (hN : InvSeriesEntry) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hO : OperatorNormBounds) (hW : WindowBound) (hT : TailBound) : LambdaComparison := by
  intro hK F hFK hFG hFD P k θ b A hl hl1 hP hk hLk hθl hθ1 hb δ hδ
  have hl4 : 0 < Real.exp (-(P / k)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hl _
  have hθ0 : 0 < θ := hl4.trans hθl
  have hq0 : 0 < Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ := div_pos hl4 hθ0
  have hq1 : Real.exp (-(P / k)) ^ (1 / 4 : ℝ) / θ < 1 := (div_lt_one hθ0).2 hθl
  have hL : (0 : ℝ) ≤ 1 - Real.exp (-(P / k)) := by linarith
  have hTB := hT hK F hFK hFG hFD P k θ b A hl hl1 hP hk hLk hθl hθ1 hb
  have hK0 := hTB.choose_spec.1
  have hKb := hTB.choose_spec.2
  have hG := geometric_choice _ δ _ hq0 hq1 hδ hK0
  have hr0 := hG.choose_spec.choose_spec.choose_spec.1
  have hr1 := hG.choose_spec.choose_spec.choose_spec.2.1
  have hc := hG.choose_spec.choose_spec.choose_spec.2.2.1
  have hrq := hG.choose_spec.choose_spec.choose_spec.2.2.2.1
  have hKr := hG.choose_spec.choose_spec.choose_spec.2.2.2.2.1
  have hcr := hG.choose_spec.choose_spec.choose_spec.2.2.2.2.2
  have hWB := hW hK F hFK hFG hFD P k θ b A hl hl1 hP hk hLk hθl hθ1 hb hG.choose_spec.choose_spec.choose
    (hG.choose_spec.choose * hG.choose ^ hG.choose_spec.choose_spec.choose) (mul_pos hc (pow_pos hr0 _))
  have hT₁0 := hWB.choose_spec.1
  have hT₁ := hWB.choose_spec.2
  have hb2 : 0 < 64 * b ^ 2 := by positivity
  refine ⟨min hWB.choose (1 / (64 * b ^ 2)), lt_min hT₁0 (by positivity), fun T hT0 hT1 hTT => ?_⟩
  have hTa : T < hWB.choose := hTT.trans_le (min_le_left _ _)
  have hTb : T < 1 / (64 * b ^ 2) := hTT.trans_le (min_le_right _ _)
  have hsb : Real.sqrt T * b ≤ 1 / 8 := by
    have hs := Real.sq_sqrt hT0.le
    have hs0 := Real.sqrt_nonneg T
    have hTb' := (lt_div_iff₀ hb2).1 hTb
    nlinarith [mul_nonneg hs0 hb.le]
  refine opNorm_le_of_entries (L := MildFramework.stepLength P k) _
    (fun ζ m n s => torusEntry hK T (Real.exp (-(P / k))) θ hT0 hT1 hl hl1 b A ζ m n s -
      r3Entry F P k θ b A ζ m n s) _ _ δ hr0 hr1 hc hδ hcr (fun ζ n s => ?_) (fun ζ m j s => ?_)
  · refine (sub_entry _ _ ζ n s).trans ?_
    refine (congrArg₂ (· - ·)
      (torus_apply hN hS hC hO hK T (Real.exp (-(P / k))) θ hT0 hT1 hl hl1 b A hθ0 hq1 hL ζ n s)
      (r3_apply hN hS hC hO F P k θ b A hP hk hθ0 hq1 hL ζ n s)).trans ?_
    rw [Finset.sum_sub_distrib]
  · refine (le_or_gt j hG.choose_spec.choose_spec.choose).elim (fun hj => ?_) (fun hj => ?_)
    · exact window_term _ _ _ _ _ j _ hr0.le hr1.le hc.le (norm_nonneg ζ) hj (hT₁ T hT0 hT1 hTa ζ m j hj s)
    · exact tail_term _ _ _ _ _ _ _ j _ hr0.le hr1.le hK0 (norm_nonneg ζ) (hrq j) hKr hj
        (hKb T hT0 hT1 hsb ζ m j s).1 (hKb T hT0 hT1 hsb ζ m j s).2

end Breakdown.Periodic
