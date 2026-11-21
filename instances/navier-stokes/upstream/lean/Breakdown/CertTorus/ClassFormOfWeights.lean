import Breakdown.CertTorus.DecayStatements

noncomputable section

namespace Breakdown.FarField

namespace ClassForm.Internal

theorem norm_le_of_weightedBound {E : Type*} [Norm E] (a : ℝ → Space → E) (γ A : ℝ) (k : ℕ)
    (hγ : γ = k) (h : WeightedBound a γ A) (s : ℝ) (y : Space) :
    ‖a s y‖ ≤ A / (1 + ‖y‖) ^ k := by
  have hpos : 0 < (1 + ‖y‖) ^ k := pow_pos (by positivity) k
  have h1 := h s y
  rw [hγ, Real.rpow_natCast] at h1
  rw [le_div_iff₀ hpos]
  linarith [mul_comm ((1 + ‖y‖) ^ k) ‖a s y‖]

theorem abs_coord_le_norm (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq]
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h

theorem eq_sum_coord_smul_unitVector (v : Space) : v = ∑ i, v i • unitVector i := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simpa [unitVector] using h.symm

theorem norm_le_three_mul_of_coords (L : Space →L[ℝ] ℝ) (B : ℝ)
    (hB : ∀ i, |L (unitVector i)| ≤ B) : ‖L‖ ≤ 3 * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hL : L v = ∑ i, v i * L (unitVector i) := by
    have h := congrArg L (eq_sum_coord_smul_unitVector v)
    rw [map_sum] at h
    simpa [smul_eq_mul] using h
  rw [hL, Real.norm_eq_abs]
  calc |∑ i, v i * L (unitVector i)| ≤ ∑ i, |v i * L (unitVector i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ‖v‖ * B := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (abs_coord_le_norm v i) (hB i) (abs_nonneg _) (norm_nonneg _)
    _ = 3 * B * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end ClassForm.Internal

open ClassForm.Internal

theorem classFormOfWeights_holds : ClassFormOfWeights := by
  intro W q ⟨A₀, h₀⟩ ⟨A₁, h₁⟩ ⟨A₂, h₂⟩ ⟨B, hq⟩
  refine ⟨max A₀ (max A₁ (max A₂ (3 * B))), ?_, ?_⟩
  · intro s y j hj
    have hpos : ∀ k : ℕ, 0 < (1 + ‖y‖) ^ k := fun k => pow_pos (by positivity) k
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      calc ‖W s y‖ ≤ A₀ / (1 + ‖y‖) ^ (0 + 1) :=
            norm_le_of_weightedBound W 1 A₀ (0 + 1) (by norm_num) h₀ s y
        _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) (hpos _).le
    · rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
      calc ‖fderiv ℝ (W s) y‖ ≤ A₁ / (1 + ‖y‖) ^ (1 + 1) :=
            norm_le_of_weightedBound (fun s y => fderiv ℝ (W s) y) 2 A₁ (1 + 1) (by norm_num)
              h₁ s y
        _ ≤ _ := div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
              (hpos _).le
    · calc ‖iteratedFDeriv ℝ 2 (W s) y‖ ≤ A₂ / (1 + ‖y‖) ^ (2 + 1) :=
            norm_le_of_weightedBound (fun s y => iteratedFDeriv ℝ 2 (W s) y) 3 A₂ (2 + 1)
              (by norm_num) h₂ s y
        _ ≤ _ := div_le_div_of_nonneg_right
              (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) (hpos _).le
  · intro s y
    have hpos : 0 < (1 + ‖y‖) ^ 3 := pow_pos (by positivity) 3
    have h := norm_le_three_mul_of_coords (fderiv ℝ (q s) y) (B / (1 + ‖y‖) ^ 3)
      (fun i => hq s y i)
    rw [← mul_div_assoc] at h
    exact h.trans (div_le_div_of_nonneg_right
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)) hpos.le)

end Breakdown.FarField
