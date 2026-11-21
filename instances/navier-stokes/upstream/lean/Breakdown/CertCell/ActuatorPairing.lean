import Breakdown.CertCell.TopStatements

noncomputable section

namespace Breakdown

namespace CertCell

private theorem eq_of_forall_close_equal_pair {x y : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, a = b ∧ |x - a| + |y - b| < ε) : x = y := by
  refine eq_of_abs_sub_le_all ?_
  intro ε hε
  obtain ⟨a, b, hab, hlt⟩ := hc ε hε
  subst hab
  have h1 : |x - y| ≤ |x - a| + |y - a| := by
    calc |x - y| = |(x - a) - (y - a)| := by ring_nf
      _ ≤ |x - a| + |y - a| := abs_sub _ _
  linarith

theorem actuatorPairing_of_solenoidal_and_gradient
    (hSol : ∀ {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
      (wt : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
      (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) {w₀ epsSup epsGradSup ratio : ℝ},
      CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio →
      ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
        (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → ∀ (M : ℝ → Space → Space), w.IsMultiplierField v G H M →
      ∀ (ψ : ℝ → Space → Space), ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2) →
      IsTimePeriodic ψ → (∃ R, ∀ σ y, R < ‖y‖ → ψ σ y = 0) →
      (∀ σ y, divergenceAt (ψ σ) y = 0) → periodPairing ψ M = multiplierRight w v G H ψ)
    (hGrad : ∀ {C : Type} {nE nM : ℕ} (w : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
      (wt : Space → ℝ) (Γ : Set Symmetry) (W : ℝ → Space → Space)
      (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) {w₀ epsSup epsGradSup ratio : ℝ},
      CoerciveWeak.IsAdmissibleWeak w P h wt W HW w₀ epsSup epsGradSup ratio →
      ∀ (b : ℝ → Space → Space), Instance.ActuatorFacts w b →
      ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
        (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → ∀ (M : ℝ → Space → Space), w.IsMultiplierField v G H M →
      ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → Space → Space, ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2) ∧
        IsTimePeriodic ψ ∧ (∃ R, ∀ σ y, R < ‖y‖ → ψ σ y = 0) ∧ (∀ σ y, divergenceAt (ψ σ) y = 0) ∧
        |periodPairing b M - periodPairing ψ M| +
          |multiplierRight w v G H b - multiplierRight w v G H ψ| < ε) :
    ActuatorPairingHolds := by
  intro C nE nM w P h wt Γ W HW w₀ epsSup epsGradSup ratio hw b hb v G H g hv M hM
  refine eq_of_forall_close_equal_pair ?_
  intro ε hε
  obtain ⟨ψ, hψ, hper, hsupp, hdiv, hlt⟩ := hGrad w P h wt Γ W HW hw b hb v G H g hv M hM ε hε
  exact ⟨periodPairing ψ M, multiplierRight w v G H ψ,
    hSol w P h wt Γ W HW hw v G H g hv M hM ψ hψ hper hsupp hdiv, hlt⟩

end CertCell

end Breakdown
