import Breakdown.Uniqueness.PressureAverageAuxField
import Breakdown.Uniqueness.PressureAverageAuxStress2

open scoped ContDiff ENNReal
open MeasureTheory Set Real Metric Filter Topology

noncomputable section

namespace Breakdown.Internal

private theorem tsupport_subset_closedBall_aux {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    {r : ℝ} (hs : ∀ x, r < ‖x‖ → f x = 0) : tsupport f ⊆ closedBall 0 r := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  rw [mem_closedBall_zero_iff]
  by_contra h
  exact hx (hs x (not_le.1 h))

private theorem secondPartial_div_eq_zero_aux {Φ : Space → Space} {r : ℝ}
    (hs : ∀ x, r < ‖x‖ → Φ x = 0) (i j : Fin 3) {y : Space} (hy : r < ‖y‖) :
    FundSol.secondPartial (divergenceAt Φ) i j y = 0 := by
  have h1 : tsupport (divergenceAt Φ) ⊆ tsupport Φ := by
    rw [PressureMollify.divergenceAt_eq_comp]
    exact (tsupport_comp_subset (map_zero _) _).trans (tsupport_fderiv_subset (𝕜 := ℝ))
  have hy' : y ∉ tsupport (divergenceAt Φ) := fun h => by
    have := tsupport_subset_closedBall_aux hs (h1 h)
    rw [mem_closedBall_zero_iff] at this
    linarith
  have h0 : iteratedFDeriv ℝ 2 (divergenceAt Φ) y = 0 := by
    by_contra hne
    exact hy' (support_iteratedFDeriv_subset 2 hne)
  simp [FundSol.secondPartial, h0]

private theorem abs_secondPartial_div_le_aux {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ)
    (i j : Fin 3) (y : Space) :
    |FundSol.secondPartial (divergenceAt Φ) i j y| ≤
      ‖PressureMollify.divergenceMap‖ * ‖iteratedFDeriv ℝ 3 Φ y‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Φ) (x := y) (n := 2)
  calc |FundSol.secondPartial (divergenceAt Φ) i j y|
      ≤ ‖iteratedFDeriv ℝ 2 (divergenceAt Φ) y‖ := PressureMollify.abs_secondPartial_le _ i j y
    _ ≤ ‖PressureMollify.divergenceMap‖ * ‖iteratedFDeriv ℝ 2 (fderiv ℝ Φ) y‖ := by
        rw [PressureMollify.divergenceAt_eq_comp]
        exact PressureMollify.divergenceMap.norm_iteratedFDeriv_comp_left
          ((hΦ.fderiv_right (m := ∞) le_rfl).contDiffAt) PressureMollify.two_le_infty
    _ = _ := by rw [h]

private theorem norm_iteratedFDeriv_three_mollify_le_aux {ϕ : Space → Space}
    (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ, 0 < ρ → ∀ y,
      ‖iteratedFDeriv ℝ 3 (FundSol.mollify ρ ϕ) y‖ ≤ C * ρ⁻¹ ^ 6 := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_mollifier_aux 3
  refine ⟨‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space)‖ * C * ∫ y, ‖ϕ y‖,
    mul_nonneg (mul_nonneg (norm_nonneg _) hC0) (integral_nonneg fun _ => norm_nonneg _),
    fun ρ hρ y => ?_⟩
  have h := norm_iteratedFDeriv_convolution_field_le hϕ.continuous hc 3
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space) (FundSol.mollifier ρ)
    (contDiff_mollifier_aux ρ) (hasCompactSupport_mollifier_aux hρ) (C * ρ⁻¹ ^ 6)
    (fun x => hC ρ hρ x) y
  calc ‖iteratedFDeriv ℝ 3 (FundSol.mollify ρ ϕ) y‖ ≤ _ := h
    _ = _ := by ring

theorem abs_secondPartial_potential_div_mollify_le {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ)
    (hc : HasCompactSupport ϕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ, 1 ≤ ρ → ∀ i j x,
      |FundSol.secondPartial (FundSol.potential (divergenceAt (FundSol.mollify ρ ϕ))) i j x| ≤
        C * ρ⁻¹ ^ 3 := by
  obtain ⟨R, C₀, hR, hC₀, hB⟩ := mollify_field_bounds hϕ hc
  obtain ⟨C₃, hC₃, h3⟩ := norm_iteratedFDeriv_three_mollify_le_aux hϕ hc
  obtain ⟨K, hK, hpot⟩ := abs_potential_le_of_support
  set D := ‖PressureMollify.divergenceMap‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  refine ⟨D * C₃ * K * (R + 1) ^ 2, by positivity, fun ρ hρ i j x => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hΦ := contDiff_mollify_field hϕ hc hρ0
  have hΦc := hasCompactSupport_mollify_field hϕ hc hρ0
  have hRρ : R ≤ R * ρ := by nlinarith
  have hsupp : ∀ y, (R + 1) * ρ < ‖y‖ → FundSol.mollify ρ ϕ y = 0 := fun y hy =>
    (hB ρ hρ y).1 (by nlinarith)
  rw [FundSol.secondPartial_potential (PressureMollify.contDiff_divergenceAt hΦ)
    (PressureMollify.hasCompactSupport_divergenceAt hΦc)]
  have hr : 0 < (R + 1) * ρ := by positivity
  have h := hpot (FundSol.secondPartial (divergenceAt (FundSol.mollify ρ ϕ)) i j)
    (D * (C₃ * ρ⁻¹ ^ 6)) ((R + 1) * ρ) hr
    (fun t => (abs_secondPartial_div_le_aux hΦ i j t).trans (by gcongr; exact h3 ρ hρ0 t))
    (fun t ht => secondPartial_div_eq_zero_aux hsupp i j ht) x
  refine h.trans ?_
  have e : D * (C₃ * ρ⁻¹ ^ 6) * K * ((R + 1) * ρ) ^ 2 =
      D * C₃ * K * (R + 1) ^ 2 * ρ⁻¹ ^ 3 * (ρ⁻¹ * (ρ⁻¹ * ρ) ^ 2) := by ring
  rw [e, inv_mul_cancel₀ hρ0.ne', one_pow, mul_one]
  have h1 : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ
  have h0 : 0 ≤ D * C₃ * K * (R + 1) ^ 2 * ρ⁻¹ ^ 3 := by positivity
  calc D * C₃ * K * (R + 1) ^ 2 * ρ⁻¹ ^ 3 * ρ⁻¹ ≤ D * C₃ * K * (R + 1) ^ 2 * ρ⁻¹ ^ 3 * 1 := by
        gcongr
    _ = _ := by ring

end Breakdown.Internal
