import Breakdown.Spectral.SpectralPowers
import Breakdown.Spectral.CompactPart
import Breakdown.Spectral.FiniteSpectrum
import Breakdown.Spectral.ProjectionAlgebra

noncomputable section

namespace Breakdown.Spectral

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

theorem exists_dichotomy_complex (T₀ C : Y →L[ℂ] Y) {b α β : ℝ} (hb : 0 ≤ b) (hbα : b ≤ α)
    (hαβ : α < β) (hT₀ : ‖T₀‖ ≤ b) (hC : IsCompactOperator C) :
    ∃ (r₁ r₂ K : ℝ) (Q : Y →L[ℂ] Y) (B : ℕ → Y →L[ℂ] Y),
      α < r₁ ∧ r₁ < r₂ ∧ r₂ < β ∧ 0 < K ∧
      Q * Q = Q ∧ Commute Q (T₀ + C) ∧ IsCompactOperator ⇑((1 : Y →L[ℂ] Y) - Q) ∧
      (∀ n : ℕ, ‖(T₀ + C) ^ n * Q‖ ≤ K * r₁ ^ n) ∧
      (∀ n : ℕ, ‖B n‖ ≤ K * r₂⁻¹ ^ n) ∧
      (∀ n : ℕ, (T₀ + C) ^ n * B n = 1 - Q) ∧
      (∀ n : ℕ, Commute (B n) (T₀ + C)) ∧ (∀ n : ℕ, Commute (B n) Q) := by
  obtain ⟨ρ₁, ρ₂, hαρ₁, h12, hρ₂β, hA⟩ := exists_annulus T₀ C hT₀ hbα hαβ hC
  set T := T₀ + C with hTdef
  have hρ₁ : 0 < ρ₁ := lt_of_le_of_lt (hb.trans hbα) hαρ₁
  have hρ₂ : 0 < ρ₂ := hρ₁.trans h12
  have hA₁ : ∀ z : ℂ, ‖z‖ = ρ₁ → z ∈ resolventSet ℂ T := fun z hz =>
    hA z hz.ge (hz.le.trans h12.le)
  have hA₂ : ∀ z : ℂ, ‖z‖ = ρ₂ → z ∈ resolventSet ℂ T := fun z hz =>
    hA z (h12.le.trans hz.ge) hz.le
  set R : ℝ := ‖T‖ + ρ₂ + 1 with hRdef
  have hρR : ρ₂ < R := by
    have := norm_nonneg T
    rw [hRdef]; linarith
  have hTR : ‖T‖ < R := by rw [hRdef]; linarith
  have hQeq : specProj T ρ₁ = specProj T ρ₂ := specProj_eq_of_annulus T hρ₁ h12.le hA
  obtain ⟨K₁, hK₁, hs₁⟩ := norm_pow_mul_specProj_le T hρ₁ hA₁
  obtain ⟨K₂, hK₂, hu₂⟩ := norm_backProj_le T hρ₂ hρR hA₂ hTR
  set Q := specProj T ρ₁ with hQdef
  set B : ℕ → Y →L[ℂ] Y := fun n => backProj T ρ₂ R n with hBdef
  set K := max K₁ K₂ with hKdef
  have hQT : Commute Q T := (commute_specProj (Commute.refl T) ρ₁).symm
  have hTB : ∀ n : ℕ, T ^ n * B n = 1 - Q := fun n => by
    rw [hQeq]; exact pow_mul_backProj T hρ₂ hρR hA₂ hTR n
  have hs : ∀ n : ℕ, ‖T ^ n * Q‖ ≤ K * ρ₁ ^ n := fun n =>
    (hs₁ n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρ₁.le n))
  have hu : ∀ n : ℕ, ‖B n‖ ≤ K * ρ₂⁻¹ ^ n := fun n =>
    (hu₂ n).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (pow_nonneg (inv_nonneg.mpr hρ₂.le) n))
  have hBT : ∀ n : ℕ, Commute (B n) T := fun n =>
    (commute_backProj (Commute.refl T) ρ₂ R n).symm
  have hQB : ∀ n : ℕ, Commute Q (B n) := fun n => commute_backProj hQT ρ₂ R n
  have hQQ : Q * Q = Q := idempotent_of_bounds T Q B hρ₁.le h12 hQT hQB hTB hs hu
  have hcpt : IsCompactOperator ⇑((1 : Y →L[ℂ] Y) - Q) :=
    isCompactOperator_one_sub_specProj T₀ C hT₀ (lt_of_le_of_lt hbα hαρ₁) hC hA₁
  exact ⟨ρ₁, ρ₂, K, Q, B, hαρ₁, h12, hρ₂β, lt_max_of_lt_left hK₁, hQQ, hQT, hcpt, hs, hu, hTB,
    hBT, fun n => (hQB n).symm⟩

end Breakdown.Spectral
