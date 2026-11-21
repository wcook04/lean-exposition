import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

namespace SecondDeriv.Internal

def tensorBilin : Space →L[ℝ] Space →L[ℝ] (Fin 3 → Fin 3 → ℝ) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (a b : Space) (j k : Fin 3) => a j * b k)
      (fun a a' b => by funext j k; simp [add_mul])
      (fun c a b => by funext j k; simp [mul_assoc])
      (fun a b b' => by funext j k; simp [mul_add])
      (fun c a b => by funext j k; simp; ring))
    1 (fun a b => by
      simp only [LinearMap.mk₂_apply, one_mul]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa using PiLp.norm_apply_le a j)
        (by simpa using PiLp.norm_apply_le b k) (abs_nonneg _) (norm_nonneg _))

theorem tensorBilin_norm_le : ‖tensorBilin‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

theorem tensorBilin_apply (a b : Space) : tensorBilin a b = fun j k => a j * b k := rfl

theorem pairTensor_eq_tensorBilin (W : ℝ → Space → Space) (s : ℝ) :
    pairTensor W W s = fun y => tensorBilin (W s y) (W s y) := by
  funext y
  rw [tensorBilin_apply]
  rfl

theorem norm_secondDirectional_le (f : Space → Space) (hf : ContDiff ℝ ∞ f) (z v w : Space) :
    ‖fderiv ℝ (fun x => fderiv ℝ (fun y => tensorBilin (f y) (f y)) x v) z w‖ ≤
      (2 * (‖f z‖ * ‖iteratedFDeriv ℝ 2 f z‖) + 2 * (‖fderiv ℝ f z‖ * ‖fderiv ℝ f z‖)) *
        (‖v‖ * ‖w‖) := by
  have hT : ContDiff ℝ ∞ (fun y => tensorBilin (f y) (f y)) :=
    (tensorBilin.contDiff.comp hf).clm_apply hf
  have hdT : DifferentiableAt ℝ (fderiv ℝ (fun y => tensorBilin (f y) (f y))) z :=
    ((contDiff_infty_iff_fderiv.1 hT).2.differentiable (by simp)) z
  have e : fderiv ℝ (fun x => fderiv ℝ (fun y => tensorBilin (f y) (f y)) x v) z w =
      iteratedFDeriv ℝ 2 (fun y => tensorBilin (f y) (f y)) z ![w, v] := by
    rw [fderiv_clm_apply hdT (differentiableAt_const v), iteratedFDeriv_two_apply]
    simp
  have hL := tensorBilin.norm_iteratedFDeriv_le_of_bilinear_of_le_one hf hf z (n := 2)
    (WithTop.coe_le_coe.2 le_top) tensorBilin_norm_le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, norm_iteratedFDeriv_zero,
    norm_iteratedFDeriv_one] at hL
  norm_num at hL
  have a2 : ‖iteratedFDeriv ℝ (2 - 0) f z‖ = ‖iteratedFDeriv ℝ 2 f z‖ := rfl
  have a1 : ‖iteratedFDeriv ℝ (2 - 1) f z‖ = ‖fderiv ℝ f z‖ := norm_iteratedFDeriv_one f
  have a0 : ‖iteratedFDeriv ℝ (2 - 2) f z‖ = ‖f z‖ := norm_iteratedFDeriv_zero
  rw [a2, a1, a0] at hL
  rw [e]
  calc _ ≤ ‖iteratedFDeriv ℝ 2 (fun y => tensorBilin (f y) (f y)) z‖ *
        ∏ i, ‖(![w, v] : Fin 2 → Space) i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ 2 (fun y => tensorBilin (f y) (f y)) z‖ * (‖v‖ * ‖w‖) := by
        rw [Fin.prod_univ_two]
        simp [mul_comm]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        linarith

theorem weight_combine {r γD γt A B M x d y : ℝ} (hr : 1 ≤ r) (h1 : γt ≤ 1 + γD) (h4 : γt ≤ 4)
    (hx0 : 0 ≤ x) (hd0 : 0 ≤ d) (hy0 : 0 ≤ y) (hx : r ^ (1 : ℝ) * x ≤ A)
    (hd : r ^ γD * d ≤ M) (hy : r ^ (2 : ℝ) * y ≤ B) :
    r ^ γt * (2 * (x * d) + 2 * (y * y)) ≤ 2 * (A * M) + 2 * (B * B) := by
  have hr0 : 0 < r := by linarith
  have e1 : r ^ γt ≤ r ^ (1 : ℝ) * r ^ γD := by
    rw [← Real.rpow_add hr0]
    exact Real.rpow_le_rpow_of_exponent_le hr h1
  have e2 : r ^ γt ≤ r ^ (2 : ℝ) * r ^ (2 : ℝ) := by
    rw [← Real.rpow_add hr0]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have p1 : r ^ γt * (x * d) ≤ A * M :=
    calc r ^ γt * (x * d) ≤ (r ^ (1 : ℝ) * r ^ γD) * (x * d) :=
          mul_le_mul_of_nonneg_right e1 (by positivity)
      _ = (r ^ (1 : ℝ) * x) * (r ^ γD * d) := by ring
      _ ≤ A * M := mul_le_mul hx hd (by positivity) (le_trans (by positivity) hx)
  have p2 : r ^ γt * (y * y) ≤ B * B :=
    calc r ^ γt * (y * y) ≤ (r ^ (2 : ℝ) * r ^ (2 : ℝ)) * (y * y) :=
          mul_le_mul_of_nonneg_right e2 (by positivity)
      _ = (r ^ (2 : ℝ) * y) * (r ^ (2 : ℝ) * y) := by ring
      _ ≤ B * B := mul_le_mul hy hy (by positivity) (le_trans (by positivity) hy)
  calc r ^ γt * (2 * (x * d) + 2 * (y * y)) = 2 * (r ^ γt * (x * d)) + 2 * (r ^ γt * (y * y)) := by
        ring
    _ ≤ 2 * (A * M) + 2 * (B * B) := by linarith

theorem secondDeriv_weight_gain (hOp : OpWeightedBound) (hK : LerayKernelBound) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ ∞ (fun p : ℝ × Space => W p.1 p.2))
    (hrep : ∀ s y v w, iteratedFDeriv ℝ 2 (W s) y ![w, v] =
      profileOp 2 (directionalTensor (directionalTensor (pairTensor W W) v) w) s y)
    {A B M γD γt : ℝ} (hA : WeightedBound W 1 A)
    (hB : WeightedBound (fun s y => fderiv ℝ (W s) y) 2 B)
    (hM : WeightedBound (fun s y => iteratedFDeriv ℝ 2 (W s) y) γD M)
    (h0 : 0 ≤ γt) (h3 : γt ≠ 3) (h1 : γt ≤ 1 + γD) (h4 : γt ≤ 4) :
    ∃ M', WeightedBound (fun s y => iteratedFDeriv ℝ 2 (W s) y) (min γt 3) M' := by
  have h3' : γt ≠ ((2 : ℕ) : ℝ) + 1 := by norm_num; exact h3
  obtain ⟨K, hK0, hKF⟩ := hOp hK 2 le_rfl γt h0 h3 h3'
  have eβ : (1 + ((2 : ℕ) : ℝ) / 2) = 2 := by norm_num
  have eγ : min γt (((2 : ℕ) : ℝ) + 1) = min γt 3 := by norm_num
  rw [eβ, eγ] at hKF
  have hA0 : 0 ≤ A := le_trans (by positivity) (hA 0 0)
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB 0 0)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0 0)
  have hc0 : 0 ≤ 2 * (A * M) + 2 * (B * B) := by positivity
  have hG : ∀ v w, WeightedBound (directionalTensor (directionalTensor (pairTensor W W) v) w) γt
      ((2 * (A * M) + 2 * (B * B)) * (‖v‖ * ‖w‖)) := by
    intro v w s z
    have hf : ContDiff ℝ ∞ (W s) := hW.comp ((contDiff_const (c := s)).prodMk contDiff_id)
    have hpt := norm_secondDirectional_le (W s) hf z v w
    have hshape : directionalTensor (directionalTensor (pairTensor W W) v) w s z =
        fderiv ℝ (fun x => fderiv ℝ (fun y => tensorBilin (W s y) (W s y)) x v) z w := by
      unfold directionalTensor
      rw [pairTensor_eq_tensorBilin]
    rw [hshape]
    have hr : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hw := weight_combine hr h1 h4 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (hA s z) (hM s z) (hB s z)
    calc (1 + ‖z‖) ^ γt * ‖fderiv ℝ (fun x => fderiv ℝ (fun y => tensorBilin (W s y) (W s y)) x v)
          z w‖ ≤ (1 + ‖z‖) ^ γt * ((2 * (‖W s z‖ * ‖iteratedFDeriv ℝ 2 (W s) z‖) +
            2 * (‖fderiv ℝ (W s) z‖ * ‖fderiv ℝ (W s) z‖)) * (‖v‖ * ‖w‖)) :=
          mul_le_mul_of_nonneg_left hpt (by positivity)
      _ = ((1 + ‖z‖) ^ γt * (2 * (‖W s z‖ * ‖iteratedFDeriv ℝ 2 (W s) z‖) +
            2 * (‖fderiv ℝ (W s) z‖ * ‖fderiv ℝ (W s) z‖))) * (‖v‖ * ‖w‖) := by ring
      _ ≤ (2 * (A * M) + 2 * (B * B)) * (‖v‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_right hw (by positivity)
  refine ⟨K * (2 * (A * M) + 2 * (B * B)), fun s y => ?_⟩
  have hpos : 0 < (1 + ‖y‖) ^ min γt 3 := by positivity
  have hbound : ‖iteratedFDeriv ℝ 2 (W s) y‖ ≤
      K * (2 * (A * M) + 2 * (B * B)) / (1 + ‖y‖) ^ min γt 3 := by
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
    have hm : m = ![m 0, m 1] := by
      funext i
      fin_cases i <;> rfl
    have hv := hKF _ _ (hG (m 1) (m 0)) s y
    rw [Fin.prod_univ_two]
    conv_lhs => rw [hm, hrep s y (m 1) (m 0)]
    calc ‖profileOp 2 (directionalTensor (directionalTensor (pairTensor W W) (m 1)) (m 0)) s y‖
        = ((1 + ‖y‖) ^ min γt 3 *
            ‖profileOp 2 (directionalTensor (directionalTensor (pairTensor W W) (m 1)) (m 0)) s y‖) /
            (1 + ‖y‖) ^ min γt 3 := by field_simp
      _ ≤ (K * ((2 * (A * M) + 2 * (B * B)) * (‖m 1‖ * ‖m 0‖))) / (1 + ‖y‖) ^ min γt 3 :=
          div_le_div_of_nonneg_right hv hpos.le
      _ = _ := by ring
  calc (1 + ‖y‖) ^ min γt 3 * ‖iteratedFDeriv ℝ 2 (W s) y‖
      ≤ (1 + ‖y‖) ^ min γt 3 * (K * (2 * (A * M) + 2 * (B * B)) / (1 + ‖y‖) ^ min γt 3) :=
        mul_le_mul_of_nonneg_left hbound hpos.le
    _ = K * (2 * (A * M) + 2 * (B * B)) := by field_simp

end SecondDeriv.Internal

open SecondDeriv.Internal in
theorem secondDerivBootstrap_of_op : OpWeightedBound → SecondDerivBootstrap := by
  intro hOp hK W hW ⟨C, hC⟩ ⟨A, hA⟩ ⟨B, hB⟩ hrep
  have hM0 : WeightedBound (fun s y => iteratedFDeriv ℝ 2 (W s) y) 0 C := fun s y => by
    rw [Real.rpow_zero, one_mul]
    exact hC 2 le_rfl s y
  obtain ⟨M1, hStrain⟩ := secondDeriv_weight_gain hOp hK W hW hrep hA hB hM0 (γt := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e1 : min (1 : ℝ) 3 = 1 := by norm_num
  rw [e1] at hStrain
  obtain ⟨M2, hM2⟩ := secondDeriv_weight_gain hOp hK W hW hrep hA hB hStrain (γt := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : min (2 : ℝ) 3 = 2 := by norm_num
  rw [e2] at hM2
  obtain ⟨M3, hM3⟩ := secondDeriv_weight_gain hOp hK W hW hrep hA hB hM2 (γt := 5 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : min (5 / 2 : ℝ) 3 = 5 / 2 := by norm_num
  rw [e3] at hM3
  obtain ⟨M4, hM4⟩ := secondDeriv_weight_gain hOp hK W hW hrep hA hB hM3 (γt := 7 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : min (7 / 2 : ℝ) 3 = 3 := by norm_num
  rw [e4] at hM4
  exact ⟨M4, hM4⟩

end Breakdown.FarField
