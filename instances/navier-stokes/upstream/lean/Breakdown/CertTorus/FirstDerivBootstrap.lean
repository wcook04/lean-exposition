import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FarField

namespace FirstDerivBootstrapInternal

theorem weightedBound_nonneg {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → Space → E}
    {γ A : ℝ} (h : WeightedBound f γ A) : 0 ≤ A :=
  le_trans (mul_nonneg (rpow_nonneg (by positivity) _) (norm_nonneg _)) (h 0 0)

theorem weightedBound_mono {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → Space → E}
    {γ γ' A : ℝ} (h : WeightedBound f γ A) (hγ : γ' ≤ γ) : WeightedBound f γ' A := by
  intro s y
  have h1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  exact le_trans (mul_le_mul_of_nonneg_right (rpow_le_rpow_of_exponent_le h1 hγ)
    (norm_nonneg _)) (h s y)

theorem hasFDerivAt_coord (f : Space → Space) (y : Space) (hf : DifferentiableAt ℝ f y)
    (j : Fin 3) :
    HasFDerivAt (fun z => f z j) ((EuclideanSpace.proj j).comp (fderiv ℝ f y)) y :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hf.hasFDerivAt

theorem fderiv_tensorField_apply (f : Space → Space) (y v : Space) (hf : DifferentiableAt ℝ f y)
    (j k : Fin 3) :
    fderiv ℝ (tensorField f f) y v j k =
      f y j * fderiv ℝ f y v k + f y k * fderiv ℝ f y v j := by
  have hjk : ∀ j k : Fin 3, HasFDerivAt (fun z => f z j * f z k)
      (f y j • (EuclideanSpace.proj k).comp (fderiv ℝ f y) +
        f y k • (EuclideanSpace.proj j).comp (fderiv ℝ f y)) y :=
    fun j k => (hasFDerivAt_coord f y hf j).mul (hasFDerivAt_coord f y hf k)
  have hrow : ∀ j : Fin 3, HasFDerivAt (fun z k => f z j * f z k)
      (ContinuousLinearMap.pi fun k => f y j • (EuclideanSpace.proj k).comp (fderiv ℝ f y) +
        f y k • (EuclideanSpace.proj j).comp (fderiv ℝ f y)) y :=
    fun j => hasFDerivAt_pi.2 fun k => hjk j k
  have hall := hasFDerivAt_pi.2 hrow
  have e : tensorField f f = fun z j k => f z j * f z k := rfl
  rw [e, hall.fderiv]
  simp

theorem norm_fderiv_tensorField_le (f : Space → Space) (y v : Space)
    (hf : DifferentiableAt ℝ f y) :
    ‖fderiv ℝ (tensorField f f) y v‖ ≤ 2 * (‖f y‖ * (‖fderiv ℝ f y‖ * ‖v‖)) := by
  have hD : ‖fderiv ℝ f y v‖ ≤ ‖fderiv ℝ f y‖ * ‖v‖ := (fderiv ℝ f y).le_opNorm v
  have hb : ∀ j k : Fin 3, |f y j * fderiv ℝ f y v k| ≤ ‖f y‖ * (‖fderiv ℝ f y‖ * ‖v‖) := by
    intro j k
    rw [abs_mul]
    exact mul_le_mul (PiLp.norm_apply_le (f y) j)
      ((PiLp.norm_apply_le (fderiv ℝ f y v) k).trans hD) (abs_nonneg _) (norm_nonneg _)
  have h0 : 0 ≤ 2 * (‖f y‖ * (‖fderiv ℝ f y‖ * ‖v‖)) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg h0).2 fun k => ?_
  rw [Real.norm_eq_abs, fderiv_tensorField_apply f y v hf j k]
  calc |f y j * fderiv ℝ f y v k + f y k * fderiv ℝ f y v j|
      ≤ |f y j * fderiv ℝ f y v k| + |f y k * fderiv ℝ f y v j| := abs_add_le _ _
    _ ≤ _ := by linarith [hb j k, hb k j]

theorem directionalTensor_weight (W : ℝ → Space → Space) (hW : ∀ s, Differentiable ℝ (W s))
    (a b A B : ℝ) (hA : WeightedBound W a A)
    (hB : WeightedBound (fun s y => fderiv ℝ (W s) y) b B) (v : Space) :
    WeightedBound (directionalTensor (pairTensor W W) v) (a + b) (2 * A * B * ‖v‖) := by
  intro s y
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hT : ‖directionalTensor (pairTensor W W) v s y‖ ≤
      2 * (‖W s y‖ * (‖fderiv ℝ (W s) y‖ * ‖v‖)) :=
    norm_fderiv_tensorField_le (W s) y v (hW s y)
  have h1 := hA s y
  have h2 : (1 + ‖y‖) ^ b * ‖fderiv ℝ (W s) y‖ ≤ B := hB s y
  have hX : 0 ≤ (1 + ‖y‖) ^ a * ‖W s y‖ := mul_nonneg (rpow_nonneg hpos.le _) (norm_nonneg _)
  have hY : 0 ≤ (1 + ‖y‖) ^ b * ‖fderiv ℝ (W s) y‖ :=
    mul_nonneg (rpow_nonneg hpos.le _) (norm_nonneg _)
  have hP : ((1 + ‖y‖) ^ a * ‖W s y‖) * ((1 + ‖y‖) ^ b * ‖fderiv ℝ (W s) y‖) ≤ A * B :=
    mul_le_mul h1 h2 hY (hX.trans h1)
  calc (1 + ‖y‖) ^ (a + b) * ‖directionalTensor (pairTensor W W) v s y‖
      ≤ (1 + ‖y‖) ^ (a + b) * (2 * (‖W s y‖ * (‖fderiv ℝ (W s) y‖ * ‖v‖))) :=
        mul_le_mul_of_nonneg_left hT (rpow_nonneg hpos.le _)
    _ = 2 * (((1 + ‖y‖) ^ a * ‖W s y‖) * ((1 + ‖y‖) ^ b * ‖fderiv ℝ (W s) y‖)) * ‖v‖ := by
        rw [rpow_add hpos]; ring
    _ ≤ 2 * (A * B) * ‖v‖ := by gcongr
    _ = 2 * A * B * ‖v‖ := by ring

theorem deriv_weight_step (hOp : OpWeightedBound) (hK : LerayKernelBound)
    (W : ℝ → Space → Space)
    (hrep : ∀ s y v, fderiv ℝ (W s) y v =
      profileOp (3 / 2) (directionalTensor (pairTensor W W) v) s y)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ3 : γ ≠ 3) (hγ2 : γ ≠ 2) (M : ℝ) (hM : 0 ≤ M)
    (hT : ∀ v, WeightedBound (directionalTensor (pairTensor W W) v) γ (M * ‖v‖)) :
    ∃ B : ℝ, WeightedBound (fun s y => fderiv ℝ (W s) y) (min γ 2) B := by
  have hγ2' : γ ≠ ((1 : ℕ) : ℝ) + 1 := by norm_num; exact hγ2
  obtain ⟨K, hK0, hKF⟩ := hOp hK 1 (by norm_num) γ hγ0 hγ3 hγ2'
  refine ⟨K * M, fun s y => ?_⟩
  have hpos : 0 < (1 + ‖y‖) ^ (min γ 2) := rpow_pos_of_pos (by positivity) _
  have e1 : (1 + ((1 : ℕ) : ℝ) / 2) = 3 / 2 := by norm_num
  have e2 : min γ (((1 : ℕ) : ℝ) + 1) = min γ 2 := by norm_num
  have hv : ∀ v, (1 + ‖y‖) ^ (min γ 2) * ‖fderiv ℝ (W s) y v‖ ≤ K * M * ‖v‖ := by
    intro v
    have h := hKF _ _ (hT v) s y
    rw [e1, e2] at h
    rw [hrep s y v]
    linarith [mul_assoc K M ‖v‖]
  have hnorm : ‖fderiv ℝ (W s) y‖ ≤ K * M / (1 + ‖y‖) ^ (min γ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (mul_nonneg hK0 hM) hpos.le)
      fun v => ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith [hv v]
  rw [le_div_iff₀ hpos] at hnorm
  show (1 + ‖y‖) ^ (min γ 2) * ‖fderiv ℝ (W s) y‖ ≤ K * M
  linarith

end FirstDerivBootstrapInternal

open FirstDerivBootstrapInternal in
theorem firstDerivBootstrap_of_op : OpWeightedBound → FirstDerivBootstrap := by
  intro hOp hK W hW hCex hAex hrep
  obtain ⟨C, hC⟩ := hCex
  obtain ⟨A, hA⟩ := hAex
  have hdiff : ∀ s, Differentiable ℝ (W s) := fun s =>
    (hW.comp ((contDiff_const (c := s)).prodMk contDiff_id)).differentiable (by simp)
  have hD0 : WeightedBound (fun s y => fderiv ℝ (W s) y) 0 C := by
    intro s y
    have h := hC 1 (by norm_num) s y
    have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := W s) (n := 0) (x := y)
    rw [zero_add, norm_iteratedFDeriv_zero] at e
    rw [← e] at h
    simpa using h
  have hA0 : 0 ≤ A := weightedBound_nonneg hA
  have hC0 : 0 ≤ C := weightedBound_nonneg hD0
  have hT0 := directionalTensor_weight W hdiff 1 0 A C hA hD0
  have e0 : (1 : ℝ) + 0 = 1 := by norm_num
  rw [e0] at hT0
  obtain ⟨B1, hB1⟩ := deriv_weight_step hOp hK W hrep 1 (by norm_num) (by norm_num)
    (by norm_num) (2 * A * C) (by positivity) hT0
  have f1 : min (1 : ℝ) 2 = 1 := by norm_num
  rw [f1] at hB1
  have hB10 : 0 ≤ B1 := weightedBound_nonneg hB1
  have hT1 := fun v => weightedBound_mono (directionalTensor_weight W hdiff 1 1 A B1 hA hB1 v)
    (show (3 / 2 : ℝ) ≤ 1 + 1 by norm_num)
  obtain ⟨B2, hB2⟩ := deriv_weight_step hOp hK W hrep (3 / 2) (by norm_num) (by norm_num)
    (by norm_num) (2 * A * B1) (by positivity) hT1
  have f2 : min (3 / 2 : ℝ) 2 = 3 / 2 := by norm_num
  rw [f2] at hB2
  have hB20 : 0 ≤ B2 := weightedBound_nonneg hB2
  have hT2 := directionalTensor_weight W hdiff 1 (3 / 2) A B2 hA hB2
  have e2 : (1 : ℝ) + 3 / 2 = 5 / 2 := by norm_num
  rw [e2] at hT2
  obtain ⟨B3, hB3⟩ := deriv_weight_step hOp hK W hrep (5 / 2) (by norm_num) (by norm_num)
    (by norm_num) (2 * A * B2) (by positivity) hT2
  have f3 : min (5 / 2 : ℝ) 2 = 2 := by norm_num
  rw [f3] at hB3
  exact ⟨B3, hB3⟩

end Breakdown.FarField
