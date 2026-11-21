import Breakdown.Frac.StTorusStepCompare
import Breakdown.Torus.CompareLambdaAssembly

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracCompareLambdaAssembly.Internal

open CompareLambdaAssembly.Internal

theorem torus_apply (α : ℝ) (hα : 1 < α) (hN : InvSeriesEntry) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hO : FracOperatorNormBounds α hα) (T lam θ : ℝ) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam ≤ 1) (b : ℝ) (A : Approximant (1 - lam) b) (hθ : 0 < θ)
    (hq : lam ^ dilExponent α / θ < 1) (hL : 0 ≤ 1 - lam) (ζ : ShellSeq (1 - lam)) (n : ℕ)
    (s : Icc (0 : ℝ) (1 - lam)) :
    ((fracTorusRestrict α (1 - lam) b T lam).comp
      ((Ring.inverse (1 - fracTorusShift α hα T lam θ hT hT1 hl hl1)).comp
        (fracTorusLambda α A T lam)) ζ) n s =
      ∑ m ∈ Finset.range (n + 1), fracTorusEntry α hα T lam θ hT hT1 hl hl1 b A ζ m n s := by
  obtain ⟨C, hC0, -, -, -, -, -, h6⟩ := hO
  have hq0 : 0 ≤ lam ^ dilExponent α / θ := div_nonneg (Real.rpow_nonneg hl.le _) hθ.le
  have hB : ∀ n, ‖fracTorusStep α hα T lam θ hT hT1 hl hl1 n‖ ≤ lam ^ dilExponent α / θ := fun n =>
    scaled_step_norm_le _ _ _ hq0
  have hshift := ((hS (Piece V (1 - lam)) (Piece V (1 - lam)) (fun _ => 0) (lam ^ dilExponent α / θ)
    (fun _ => by simpa using hq0) hq0).2.2.1 _ hB).1
  have hnorm : ‖seqShift (fracTorusStep α hα T lam θ hT hT1 hl hl1)‖ < 1 :=
    (h6 T lam θ hT hT1 hl hl1 hθ).trans_lt hq
  have hinv := hN (Piece V (1 - lam)) (fracTorusStep α hα T lam θ hT hT1 hl hl1) hnorm hshift
  have hR0 := restrictTorusFun_bound.choose_spec.1
  have hR : ∀ μ, ‖pieceComp (1 - lam) (restrictTorus μ b)‖ ≤ restrictTorusFun_bound.choose :=
    fun μ => (hC _ _ (1 - lam) (restrictTorus μ b) hL).2.trans (LinearMap.mkContinuous_norm_le _ hR0 _)
  have hRf := (hS (Piece V (1 - lam)) (Piece ShellData (1 - lam))
    (fun n => pieceComp (1 - lam) (restrictTorus (simScale α (stepScale T lam n)) b)) _
    (fun n => hR _) hR0).1
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  unfold fracTorusRestrict
  rw [hRf, (hC _ _ _ _ hL).1]
  change restrictTorus _ b
    ((Ring.inverse (1 - seqShift (fracTorusStep α hα T lam θ hT hT1 hl hl1))
      (fracTorusLambda α A T lam ζ)) n s) = _
  rw [hinv, ContinuousMap.coe_sum, Finset.sum_apply, map_sum]
  rfl

theorem r3_apply (α : ℝ) (hα : 1 < α) (hN : InvSeriesEntry) (hS : SeqOpSpec) (hC : PieceCompSpec)
    (hO : FracOperatorNormBounds α hα) (F : ScaledMildFramework Freq.X (dilExponent α)) (P : ℝ)
    (k : ℕ) (θ b : ℝ) (A : Approximant (MildFramework.stepLength P k) b) (hP : 0 < P) (hk : 0 < k)
    (hθ : 0 < θ) (hq : Real.exp (-(P / k)) ^ dilExponent α / θ < 1)
    (hL : 0 ≤ MildFramework.stepLength P k) (ζ : ShellSeq (MildFramework.stepLength P k)) (n : ℕ)
    (s : Icc (0 : ℝ) (MildFramework.stepLength P k)) :
    ((r3Restrict _ b).comp ((Ring.inverse (1 - fracR3Shift F P k θ)).comp (fracR3Lambda α A)) ζ) n s =
      ∑ m ∈ Finset.range (n + 1), fracR3Entry α F P k θ b A ζ m n s := by
  obtain ⟨C, hC0, -, -, -, -, h5, -⟩ := hO
  have hq0 : 0 ≤ ‖fracR3Step F P k θ 0‖ := norm_nonneg _
  have hB : ∀ n, ‖fracR3Step F P k θ n‖ ≤ ‖fracR3Step F P k θ 0‖ := fun _ => le_rfl
  have hshift := ((hS (Piece Freq.X (MildFramework.stepLength P k))
    (Piece Freq.X (MildFramework.stepLength P k)) (fun _ => 0) _
    (fun _ => by simp) hq0).2.2.1 _ hB).1
  have hnorm : ‖seqShift (fracR3Step F P k θ)‖ < 1 := (h5 F P k θ hP hk hθ).trans_lt hq
  have hinv := hN (Piece Freq.X (MildFramework.stepLength P k)) (fracR3Step F P k θ) hnorm hshift
  have hR : ∀ _n : ℕ, ‖pieceComp (MildFramework.stepLength P k) (restrictR3 b)‖ ≤ ‖restrictR3 b‖ :=
    fun _ => (hC _ _ _ (restrictR3 b) hL).2
  have hRf := (hS (Piece Freq.X (MildFramework.stepLength P k))
    (Piece ShellData (MildFramework.stepLength P k))
    (fun _ => pieceComp (MildFramework.stepLength P k) (restrictR3 b)) _ hR (norm_nonneg _)).1
  have e1 : ∀ g : R3Seq (MildFramework.stepLength P k), (r3Restrict _ b g) n s = restrictR3 b (g n s) :=
    fun g => by unfold r3Restrict; rw [hRf, (hC _ _ _ _ hL).1]
  refine (e1 ((Ring.inverse (1 - seqShift (fracR3Step F P k θ))) (fracR3Lambda α A ζ))).trans ?_
  rw [hinv]
  refine (congrArg (restrictR3 b) (ContinuousMap.sum_apply _ _ s)).trans ?_
  refine (map_sum (restrictR3 b) _ _).trans ?_
  exact Finset.sum_congr rfl fun m _ => rfl

theorem shell_small (α T b c : ℝ) (hα : 0 < α) (hT0 : 0 < T) (hb : 0 < b)
    (hc : c = 1 / (64 * b ^ 2)) (hTb : T < c ^ α) : Real.sqrt (simScale α T) * b ≤ 1 / 8 := by
  have hb2 : 0 < 64 * b ^ 2 := by positivity
  have hc0 : 0 < c := by rw [hc]; positivity
  have hS : simScale α T < c := by
    have h1 := Real.rpow_lt_rpow hT0.le hTb (by positivity : (0 : ℝ) < 1 / α)
    unfold simScale
    rw [one_div α]
    rwa [one_div α, Real.rpow_rpow_inv hc0.le hα.ne'] at h1
  have hS0 : 0 ≤ simScale α T := Real.rpow_nonneg hT0.le _
  rw [hc] at hS
  have hs := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg (simScale α T)
  have hTb' := (lt_div_iff₀ hb2).1 hS
  nlinarith [mul_nonneg hs0 hb.le]

end FracCompareLambdaAssembly.Internal

open CompareLambdaAssembly.Internal FracCompareLambdaAssembly.Internal in
theorem fracLambdaComparison (α : ℝ) (hα : 1 < α) (hN : InvSeriesEntry) (hS : SeqOpSpec)
    (hC : PieceCompSpec) (hO : FracOperatorNormBounds α hα) (hW : FracWindowBound α hα)
    (hT : FracTailBound α hα) : FracLambdaComparison α hα := by
  intro F hFK hFG hFD P k θ b A hl hl1 hP hk hLk hθl hθ1 hb δ hδ
  have hl4 : 0 < Real.exp (-(P / k)) ^ dilExponent α := Real.rpow_pos_of_pos hl _
  have hθ0 : 0 < θ := hl4.trans hθl
  have hq0 : 0 < Real.exp (-(P / k)) ^ dilExponent α / θ := div_pos hl4 hθ0
  have hq1 : Real.exp (-(P / k)) ^ dilExponent α / θ < 1 := (div_lt_one hθ0).2 hθl
  have hL : (0 : ℝ) ≤ 1 - Real.exp (-(P / k)) := by linarith
  have hTB := hT F hFK hFG hFD P k θ b A hl hl1 hP hk hLk hθl hθ1 hb
  have hK0 := hTB.choose_spec.1
  have hKb := hTB.choose_spec.2
  have hG := geometric_choice _ δ _ hq0 hq1 hδ hK0
  have hr0 := hG.choose_spec.choose_spec.choose_spec.1
  have hr1 := hG.choose_spec.choose_spec.choose_spec.2.1
  have hc := hG.choose_spec.choose_spec.choose_spec.2.2.1
  have hrq := hG.choose_spec.choose_spec.choose_spec.2.2.2.1
  have hKr := hG.choose_spec.choose_spec.choose_spec.2.2.2.2.1
  have hcr := hG.choose_spec.choose_spec.choose_spec.2.2.2.2.2
  have hWB := hW F hFK hFG hFD P k θ b A hl hl1 hP hk hLk hθl hθ1 hb hG.choose_spec.choose_spec.choose
    (hG.choose_spec.choose * hG.choose ^ hG.choose_spec.choose_spec.choose) (mul_pos hc (pow_pos hr0 _))
  have hT₁0 := hWB.choose_spec.1
  have hT₁ := hWB.choose_spec.2
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hc64 : 0 < (1 / (64 * b ^ 2)) ^ α := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min hWB.choose ((1 / (64 * b ^ 2)) ^ α), lt_min hT₁0 hc64, fun T hT0 hT1 hTT => ?_⟩
  have hTa : T < hWB.choose := hTT.trans_le (min_le_left _ _)
  have hTb : T < (1 / (64 * b ^ 2)) ^ α := hTT.trans_le (min_le_right _ _)
  have hsb : Real.sqrt (simScale α T) * b ≤ 1 / 8 := shell_small α T b _ hα0 hT0 hb rfl hTb
  refine opNorm_le_of_entries (L := MildFramework.stepLength P k) _
    (fun ζ m n s => fracTorusEntry α hα T (Real.exp (-(P / k))) θ hT0 hT1 hl hl1 b A ζ m n s -
      fracR3Entry α F P k θ b A ζ m n s) _ _ δ hr0 hr1 hc hδ hcr (fun ζ n s => ?_) (fun ζ m j s => ?_)
  · refine (sub_entry _ _ ζ n s).trans ?_
    refine (congrArg₂ (· - ·)
      (torus_apply α hα hN hS hC hO T (Real.exp (-(P / k))) θ hT0 hT1 hl hl1 b A hθ0 hq1 hL ζ n s)
      (r3_apply α hα hN hS hC hO F P k θ b A hP hk hθ0 hq1 hL ζ n s)).trans ?_
    rw [Finset.sum_sub_distrib]
  · refine (le_or_gt j hG.choose_spec.choose_spec.choose).elim (fun hj => ?_) (fun hj => ?_)
    · exact window_term _ _ _ _ _ j _ hr0.le hr1.le hc.le (norm_nonneg ζ) hj
        (hT₁ T hT0 hT1 hTa ζ m j hj s)
    · exact tail_term _ _ _ _ _ _ _ j _ hr0.le hr1.le hK0 (norm_nonneg ζ) (hrq j) hKr hj
        (hKb T hT0 hT1 hsb ζ m j s).1 (hKb T hT0 hT1 hsb ζ m j s).2

end Breakdown.Periodic
