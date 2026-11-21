import Breakdown.CertCell.BridgeStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal

theorem latticeHarmonic_of_halfTurnPhase (m : ℕ) (hm : 1 ≤ m) (ξ : ℤ × ℤ)
    (hL : IsLatticeHarmonic m ξ ↔ ((m : ℤ) ∣ ξ.2 ∧ Even (ξ.1 + ξ.2 / m)))
    (h : Complex.exp (((ξ.2 * (Real.pi / m) + 2 * Real.pi * ξ.1 * (1 / 2) : ℝ) : ℂ) * Complex.I) = 1) :
    IsLatticeHarmonic m ξ := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (((ξ.2 * (Real.pi / m) + 2 * Real.pi * ξ.1 * (1 / 2) : ℝ) : ℂ))
      = (((n * (2 * Real.pi)) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    rw [hn]
    push_cast
    ring
  have hreal : (ξ.2 : ℝ) * (Real.pi / m) + 2 * Real.pi * ξ.1 * (1 / 2) = n * (2 * Real.pi) :=
    Complex.ofReal_injective hc
  have h3 : (ξ.2 : ℝ) / m + ξ.1 = 2 * n := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    linear_combination hreal
  have h4 : (ξ.2 : ℝ) = m * (2 * n - ξ.1) := by
    have hsplit : (ξ.2 : ℝ) = ((ξ.2 : ℝ) / m) * m := (div_mul_cancel₀ _ hmR.ne').symm
    rw [hsplit, show (ξ.2 : ℝ) / m = 2 * n - ξ.1 by linarith]
    ring
  have h5 : ξ.2 = (m : ℤ) * (2 * n - ξ.1) := by exact_mod_cast h4
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hmR.ne'
  rw [hL]
  refine ⟨⟨_, h5⟩, ?_⟩
  rw [h5, Int.mul_ediv_cancel_left _ hm0]
  exact ⟨n, by ring⟩

end Internal

theorem classSupport (hO : ModeOffLatticeHolds) (hL : LabelArithmeticHolds) : ClassSupportHolds := by
  intro Γ m P v G H g hC hP ξ hξ
  obtain ⟨γ, hγΓ, hγ1, hγ2⟩ := hC.twisted
  have hinv : ∀ᵐ z : ℝ × Space, v (z.1 + 1 / 2) (axialRot (Real.pi / m) z.2)
      = axialRot (Real.pi / m) (v z.1 z.2) := by
    filter_upwards [hP.invariant γ hγΓ] with z hz
    simpa only [hγ1, hγ2] using hz
  refine hO Γ P v G H g hP (Real.pi / m) (1 / 2) hinv ξ ?_
  intro h1
  exact hξ (Internal.latticeHarmonic_of_halfTurnPhase m hC.order_pos ξ ((hL m hC.order_pos).2.2.2 ξ) h1)

end Bridge

end CertCell

end Breakdown
