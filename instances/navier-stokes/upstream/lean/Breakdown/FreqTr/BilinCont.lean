import Breakdown.FreqTr.Phi

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.BilinCont

theorem phiFactor_mul_heatFactor (s : ℝ) {t : ℝ} (ht : 0 ≤ t) (ξ : Space) :
    phiFactor s ξ * heatFactor t ξ = phiFactor (s + t) ξ := by
  unfold phiFactor heatFactor
  rw [max_eq_left ht, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem phiX_heatX (h6 : FieldOpRealized) (h7 : HeatSemigroup) {s t : ℝ} (hs : 0 < s)
    (ht : 0 ≤ t) (ψ : X) : phiX s (heatX t ψ) = phiX (s + t) ψ := by
  have e1 : phiX s (heatX t ψ) = toPhys (fieldOp id
      (fun ξ => phiFactor s ξ • ContinuousLinearMap.id ℝ CSpace) ((heatX t ψ : X) : L2C)) := rfl
  have e2 : phiX (s + t) ψ = toPhys (fieldOp id
      (fun ξ => phiFactor (s + t) ξ • ContinuousLinearMap.id ℝ CSpace) (ψ : L2C)) := rfl
  rw [e1, e2, h7.2.2.2.2.2 t ψ]
  congr 1
  apply Lp.ext
  have ha := Internal.Phi.scalarOp_ae h6 (Internal.Phi.continuous_phiFactor s) (Internal.Phi.phiFactor_le hs)
    (heatL2 t (ψ : L2C))
  have hb : (heatL2 t (ψ : L2C) : Space → CSpace) =ᵐ[volume] fun ξ => heatFactor t ξ • (ψ : L2C) ξ :=
    Internal.Phi.scalarOp_ae h6 (Internal.Phi.continuous_heatFactor t) (Internal.Phi.heatFactor_le t) (ψ : L2C)
  have hc := Internal.Phi.scalarOp_ae h6 (Internal.Phi.continuous_phiFactor (s + t))
    (Internal.Phi.phiFactor_le (add_pos_of_pos_of_nonneg hs ht)) (ψ : L2C)
  filter_upwards [ha, hb, hc] with ξ a b c
  rw [a, b, c, smul_smul, phiFactor_mul_heatFactor s ht]

theorem bilinX_spec (h1 : BilinExists) {τ : ℝ} (hτ : 0 < τ) : BilinSpec τ (bilinX τ) := by
  have h : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, h1 τ hτ⟩
  rw [bilinX, dif_pos h]
  exact h.2.choose_spec

theorem bilinX_shift (h1 : BilinExists) (h6 : FieldOpRealized) (h7 : HeatSemigroup) {s τ : ℝ}
    (hs : 0 < s) (hsτ : s ≤ τ) (u v : X) : bilinX τ u v = heatX (τ - s) (bilinX s u v) := by
  have ht : 0 ≤ τ - s := sub_nonneg.mpr hsτ
  have hτ : 0 < τ := lt_of_lt_of_le hs hsτ
  have hst : s + (τ - s) = τ := by ring
  have hφ : ∀ ψ : X, phiX s (heatX (τ - s) ψ) = phiX τ ψ := fun ψ =>
    (phiX_heatX h6 h7 hs ht ψ).trans (congrArg (fun r => phiX r ψ) hst)
  apply ext_inner_right ℝ
  intro ψ
  rw [bilinX_spec h1 hτ u v ψ, h7.2.2.2.2.1 (τ - s), bilinX_spec h1 hs u v]
  unfold bilinForm
  rw [hφ]

end Internal.BilinCont

open Internal.BilinCont in
theorem bilinContinuous (h1 : BilinExists) (_h2 : BilinBound) (_h3 : TrilinearBound)
    (_h4 : PhiBounds) (_h5 : PhiVelocity) (h6 : FieldOpRealized) (h7 : HeatSemigroup) :
    BilinContinuous := by
  intro u v τ₀ hτ₀
  have hτ : (0 : ℝ) < τ₀ := hτ₀
  have hs : 0 < τ₀ / 2 := by positivity
  have hc : ContinuousAt (fun t => heatX t (bilinX (τ₀ / 2) u v)) (τ₀ - τ₀ / 2) :=
    (h7.2.2.2.1 (bilinX (τ₀ / 2) u v)).continuousAt (Ici_mem_nhds (by linarith))
  have hcont : ContinuousAt (fun τ => heatX (τ - τ₀ / 2) (bilinX (τ₀ / 2) u v)) τ₀ :=
    ContinuousAt.comp_of_eq (g := fun t => heatX t (bilinX (τ₀ / 2) u v)) (f := fun τ => τ - τ₀ / 2)
      hc (continuous_sub_right (τ₀ / 2)).continuousAt rfl
  have heq : (fun τ => heatX (τ - τ₀ / 2) (bilinX (τ₀ / 2) u v)) =ᶠ[nhds τ₀]
      (fun τ => bilinX τ u v) := by
    filter_upwards [Ioi_mem_nhds (show τ₀ / 2 < τ₀ by linarith)] with τ hτ'
    exact (bilinX_shift h1 h6 h7 hs (le_of_lt hτ') u v).symm
  exact (hcont.congr heq).continuousWithinAt

end Breakdown.Freq
