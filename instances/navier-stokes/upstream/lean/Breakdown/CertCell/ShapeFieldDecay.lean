import Breakdown.CertCell.ShapeKeyTime

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

theorem keyVector_time_eq_smul (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) :
    keyVector P κ A σ =
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) • keyVector P κ A 0 := by
  funext y
  have h := keyTimeShift_holds P κ A 0 σ y
  rw [zero_add] at h
  rw [h]
  funext i
  simp [Pi.smul_apply, smul_eq_mul]

theorem keyVector_uniform_bounds (P : ShapeParams) (κ : FieldKey) (A : KeyAmp)
    (h : IsKeyFieldDecay (keyVector P κ A 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y, ‖keyVector P κ A σ y‖ ≤ C / (1 + ‖y‖) ∧
      ‖fderiv ℝ (keyVector P κ A σ) y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ (keyVector P κ A σ)) y‖ ≤ C / (1 + ‖y‖) ^ 3 := by
  obtain ⟨C, hC⟩ := h.bound
  have hC0 : 0 ≤ C := by
    have h0 := (hC 0).1
    rw [norm_zero, add_zero, div_one] at h0
    exact (norm_nonneg _).trans h0
  refine ⟨C, hC0, fun σ y => ?_⟩
  set c : ℂ := Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) with hc
  have hcn : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hf : keyVector P κ A σ = c • keyVector P κ A 0 := keyVector_time_eq_smul P κ A σ
  have hd : fderiv ℝ (keyVector P κ A σ) = c • fderiv ℝ (keyVector P κ A 0) := by
    funext x
    rw [hf, fderiv_const_smul_field]
  have hdd : fderiv ℝ (fderiv ℝ (keyVector P κ A σ)) y = c • fderiv ℝ (fderiv ℝ (keyVector P κ A 0)) y := by
    rw [hd, fderiv_const_smul_field]
    rfl
  obtain ⟨h1, h2, h3⟩ := hC y
  refine ⟨?_, ?_, ?_⟩
  · rw [hf, Pi.smul_apply, norm_smul, hcn, one_mul]
    exact h1
  · rw [hd, Pi.smul_apply, norm_smul, hcn, one_mul]
    exact h2
  · rw [hdd, norm_smul, hcn, one_mul]
    exact h3

end Internal

theorem fieldDecay_of (hone : TypeOneKeyDecay) (htwo : TypeTwoKeyDecay) (hsone : TypeOneKeySmooth)
    (hstwo : TypeTwoKeySmooth) : FieldDecay := by
  intro P D hP hD
  have hkey : ∀ κ, ∃ C : ℝ, κ ∈ D.keys → 0 ≤ C ∧ ∀ σ y, ‖keyVector P κ (D.amp κ) σ y‖ ≤ C / (1 + ‖y‖) ∧
      ‖fderiv ℝ (keyVector P κ (D.amp κ) σ) y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ (keyVector P κ (D.amp κ) σ)) y‖ ≤ C / (1 + ‖y‖) ^ 3 := by
    intro κ
    by_cases hκ : κ ∈ D.keys
    · have hdec : IsKeyFieldDecay (keyVector P κ (D.amp κ) 0) := by
        by_cases hl : κ.label.1 = 0
        · exact htwo P D κ 0 hP hD hκ hl
        · exact hone P D κ 0 hP hD hκ hl
      obtain ⟨C, hC0, hC⟩ := Internal.keyVector_uniform_bounds P κ (D.amp κ) hdec
      exact ⟨C, fun _ => ⟨hC0, hC⟩⟩
    · exact ⟨0, fun h => absurd h hκ⟩
  choose C hC using hkey
  have hdiff : ∀ κ ∈ D.keys, ∀ σ, Differentiable ℝ (keyVector P κ (D.amp κ) σ) := by
    intro κ hκ σ
    by_cases hl : κ.label.1 = 0
    · exact (hstwo P D κ σ hP hD hκ hl).smooth.differentiable one_ne_zero
    · exact (hsone P D κ σ hP hD hκ hl).smooth.differentiable one_ne_zero
  set S : ℝ := ∑ κ ∈ D.keys, C κ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun κ hκ => (hC κ hκ).1
  set K₁ : ℝ := ‖realPartVec‖ with hK₁
  set K₂ : ℝ := ‖ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec‖ with hK₂
  have hK₁0 : 0 ≤ K₁ := norm_nonneg _
  have hK₂0 : 0 ≤ K₂ := norm_nonneg _
  refine ⟨(K₁ + K₂) * S, fun σ y => ?_⟩
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have hsum : ∀ n : ℕ, ∑ κ ∈ D.keys, C κ / (1 + ‖y‖) ^ n = S / (1 + ‖y‖) ^ n := by
    intro n
    rw [hS, Finset.sum_div]
  have hfin : ∀ n : ℕ, ∀ a : ℝ, 0 ≤ a → a ≤ K₁ + K₂ → a * (S / (1 + ‖y‖) ^ n) ≤ (K₁ + K₂) * S / (1 + ‖y‖) ^ n := by
    intro n a ha haK
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right haK (div_nonneg hS0 (pow_nonneg hpos.le n))
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ‖shapeInfoField P D σ y‖ ≤ K₁ * ‖complexField P D σ y‖ := realPartVec.le_opNorm _
    have h2 : ‖complexField P D σ y‖ ≤ S / (1 + ‖y‖) ^ 1 := by
      rw [← hsum 1]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ => ?_)
      rw [pow_one]
      exact ((hC κ hκ).2 σ y).1
    have h3 := hfin 1 K₁ hK₁0 (le_add_of_nonneg_right hK₂0)
    rw [pow_one] at h2 h3
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hK₁0).trans h3)
  · have hder : HasFDerivAt (complexField P D σ)
        (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y) y := by
      have := HasFDerivAt.fun_sum (u := D.keys) (A := fun κ => keyVector P κ (D.amp κ) σ)
        (A' := fun κ => fderiv ℝ (keyVector P κ (D.amp κ) σ) y) (x := y)
        (fun κ hκ => (hdiff κ hκ σ y).hasFDerivAt)
      exact this
    have hF : fderiv ℝ (shapeInfoField P D σ) y =
        realPartVec.comp (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y) :=
      (realPartVec.hasFDerivAt.comp y hder).fderiv
    rw [hF]
    have h1 := realPartVec.opNorm_comp_le (∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y)
    have h2 : ‖∑ κ ∈ D.keys, fderiv ℝ (keyVector P κ (D.amp κ) σ) y‖ ≤ S / (1 + ‖y‖) ^ 2 := by
      rw [← hsum 2]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ hκ => ((hC κ hκ).2 σ y).2.1)
    exact h1.trans ((mul_le_mul_of_nonneg_left h2 hK₁0).trans
      (hfin 2 K₁ hK₁0 (le_add_of_nonneg_right hK₂0)))
  · have h2 : ∑ κ ∈ D.keys, ‖(ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).comp
        (keyHess P κ (D.amp κ) σ y)‖ ≤ K₂ * (S / (1 + ‖y‖) ^ 3) := by
      rw [← hsum 3, Finset.mul_sum]
      refine Finset.sum_le_sum fun κ hκ => ?_
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left ((hC κ hκ).2 σ y).2.2 hK₂0)
    exact (norm_sum_le _ _).trans (h2.trans (hfin 3 K₂ hK₂0 (le_add_of_nonneg_left hK₁0)))

end GivenShape

end CertCell

end Breakdown
