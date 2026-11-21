import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace FracInternal.BilinBound

open Internal.BilinExists

variable {α : ℝ}

private theorem integrable_density (h2 : FracPhiBounds α) {τ : ℝ} (hτ : 0 < τ) (u v ψ : X) :
    Integrable (triDensity u v (fracPhiX α τ ψ : Space → Space)) volume := by
  obtain ⟨C, hC⟩ := trilinear_holds
  obtain ⟨D, hD⟩ := h2
  exact (hC u v _ (Lp.memLp _) (hD τ hτ ψ).1).1

private theorem tri_phi_add (h2 : FracPhiBounds α) {τ : ℝ} (hτ : 0 < τ) (u v ψ ψ' : X) :
    trilinear u v (fracPhiX α τ (ψ + ψ') : Space → Space) =
      trilinear u v (fracPhiX α τ ψ : Space → Space) +
        trilinear u v (fracPhiX α τ ψ' : Space → Space) := by
  have h : (fracPhiX α τ (ψ + ψ') : Space → Space) =ᵐ[volume]
      (fracPhiX α τ ψ : Space → Space) + (fracPhiX α τ ψ' : Space → Space) := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  rw [trilinear_congr u v h, trilinear_eq, triDensity_add_right]
  exact integral_add (integrable_density h2 hτ u v ψ) (integrable_density h2 hτ u v ψ')

private theorem tri_phi_smul (α τ c : ℝ) (u v ψ : X) :
    trilinear u v (fracPhiX α τ (c • ψ) : Space → Space) =
      c * trilinear u v (fracPhiX α τ ψ : Space → Space) := by
  have h : (fracPhiX α τ (c • ψ) : Space → Space) =ᵐ[volume]
      c • (fracPhiX α τ ψ : Space → Space) := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  rw [trilinear_congr u v h, trilinear_eq, triDensity_smul_right]
  exact integral_smul c _

private theorem form_symm (α τ : ℝ) (u v ψ : X) :
    fracBilinForm α τ u v ψ = fracBilinForm α τ v u ψ := by
  simp only [fracBilinForm, add_comm]

private theorem form_add_left (h2 : FracPhiBounds α) {τ : ℝ} (hτ : 0 < τ) (u u' v ψ : X) :
    fracBilinForm α τ (u + u') v ψ = fracBilinForm α τ u v ψ + fracBilinForm α τ u' v ψ := by
  have hi := integrable_density h2 hτ
  simp only [fracBilinForm, trilinear_add_left (hi u v ψ) (hi u' v ψ),
    trilinear_add_mid (hi v u ψ) (hi v u' ψ)]
  ring

private theorem form_smul_left (α τ c : ℝ) (u v ψ : X) :
    fracBilinForm α τ (c • u) v ψ = c * fracBilinForm α τ u v ψ := by
  simp only [fracBilinForm, trilinear_smul_left, trilinear_smul_mid]
  ring

private theorem form_add_right (h2 : FracPhiBounds α) {τ : ℝ} (hτ : 0 < τ) (u v ψ ψ' : X) :
    fracBilinForm α τ u v (ψ + ψ') = fracBilinForm α τ u v ψ + fracBilinForm α τ u v ψ' := by
  simp only [fracBilinForm, tri_phi_add h2 hτ]
  ring

private theorem form_smul_right (α τ c : ℝ) (u v ψ : X) :
    fracBilinForm α τ u v (c • ψ) = c * fracBilinForm α τ u v ψ := by
  simp only [fracBilinForm, tri_phi_smul]
  ring

private theorem sqrt_le (hα : 1 < α) (h2 : FracPhiBounds α) : ∃ D : ℝ, 0 ≤ D ∧ ∀ τ, 0 < τ →
    ∀ ψ : X, Real.sqrt ((eLpNorm (fracPhiX α τ ψ : Space → Space) 2 volume).toReal *
      (eLpNorm (fracPhiX α τ ψ : Space → Space) 6 volume).toReal) ≤
        D * τ ^ (-(3 / (4 * α))) * ‖ψ‖ := by
  obtain ⟨D, hD⟩ := h2
  have hα0 : α ≠ 0 := by linarith
  refine ⟨|D|, abs_nonneg D, fun τ hτ ψ => ?_⟩
  obtain ⟨-, ha, hb⟩ := hD τ hτ ψ
  have ha' : (eLpNorm (fracPhiX α τ ψ : Space → Space) 2 volume).toReal ≤
      |D| * τ ^ (-(1 / (2 * α))) * ‖ψ‖ := by
    refine ha.trans ?_
    gcongr
    exact le_abs_self D
  have hb' : (eLpNorm (fracPhiX α τ ψ : Space → Space) 6 volume).toReal ≤
      |D| * τ ^ (-(1 / α)) * ‖ψ‖ := by
    refine hb.trans ?_
    gcongr
    exact le_abs_self D
  have hpow : τ ^ (-(1 / (2 * α))) * τ ^ (-(1 / α)) =
      τ ^ (-(3 / (4 * α))) * τ ^ (-(3 / (4 * α))) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]
    congr 1
    field_simp
    ring
  have hprod : (eLpNorm (fracPhiX α τ ψ : Space → Space) 2 volume).toReal *
      (eLpNorm (fracPhiX α τ ψ : Space → Space) 6 volume).toReal ≤
        (|D| * τ ^ (-(3 / (4 * α))) * ‖ψ‖) ^ 2 := by
    calc _ ≤ (|D| * τ ^ (-(1 / (2 * α))) * ‖ψ‖) * (|D| * τ ^ (-(1 / α)) * ‖ψ‖) :=
          mul_le_mul ha' hb' ENNReal.toReal_nonneg (le_trans ENNReal.toReal_nonneg ha')
      _ = |D| ^ 2 * (τ ^ (-(1 / (2 * α))) * τ ^ (-(1 / α))) * ‖ψ‖ ^ 2 := by ring
      _ = (|D| * τ ^ (-(3 / (4 * α))) * ‖ψ‖) ^ 2 := by rw [hpow]; ring
  calc _ ≤ Real.sqrt ((|D| * τ ^ (-(3 / (4 * α))) * ‖ψ‖) ^ 2) := Real.sqrt_le_sqrt hprod
    _ = _ := Real.sqrt_sq (by positivity)

private theorem form_bound (hα : 1 < α) (h2 : FracPhiBounds α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ →
    ∀ u v ψ : X, |fracBilinForm α τ u v ψ| ≤ K * τ ^ (-(3 / (4 * α))) * ‖u‖ * ‖v‖ * ‖ψ‖ := by
  obtain ⟨D, hD0, hD⟩ := sqrt_le hα h2
  obtain ⟨C, hC⟩ := trilinear_holds
  refine ⟨|C| * D, by positivity, fun τ hτ u v ψ => ?_⟩
  have hS := hD τ hτ ψ
  set S := Real.sqrt ((eLpNorm (fracPhiX α τ ψ : Space → Space) 2 volume).toReal *
      (eLpNorm (fracPhiX α τ ψ : Space → Space) 6 volume).toReal) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hw6 := (h2.choose_spec τ hτ ψ).1
  have t1 : |trilinear u v (fracPhiX α τ ψ : Space → Space)| ≤ |C| * ‖u‖ * ‖v‖ * S := by
    refine (hC u v _ (Lp.memLp _) hw6).2.trans ?_
    gcongr
    exact le_abs_self C
  have t2 : |trilinear v u (fracPhiX α τ ψ : Space → Space)| ≤ |C| * ‖u‖ * ‖v‖ * S := by
    refine (hC v u _ (Lp.memLp _) hw6).2.trans ?_
    rw [mul_right_comm (|C|) ‖u‖ ‖v‖]
    gcongr
    exact le_abs_self C
  have e : |fracBilinForm α τ u v ψ| = (1 / 2 : ℝ) *
      |trilinear u v (fracPhiX α τ ψ : Space → Space) +
        trilinear v u (fracPhiX α τ ψ : Space → Space)| := by
    rw [fracBilinForm, abs_mul]
    norm_num
  rw [e]
  calc _ ≤ (1 / 2 : ℝ) * (|trilinear u v (fracPhiX α τ ψ : Space → Space)| +
        |trilinear v u (fracPhiX α τ ψ : Space → Space)|) := by gcongr; exact abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (|C| * ‖u‖ * ‖v‖ * S + |C| * ‖u‖ * ‖v‖ * S) := by gcongr
    _ = |C| * ‖u‖ * ‖v‖ * S := by ring
    _ ≤ |C| * ‖u‖ * ‖v‖ * (D * τ ^ (-(3 / (4 * α))) * ‖ψ‖) := by gcongr
    _ = _ := by ring

end FracInternal.BilinBound

open Internal.BilinExists FracInternal.BilinBound in
theorem fracBilinExistsBound (α : ℝ) (hα : 1 < α) (h1 : FracPhiBounds α) :
    FracBilinExists α ∧ FracBilinBound α := by
  obtain ⟨K, hK0, hK⟩ := form_bound hα h1
  have hB : ∀ τ, 0 < τ → ∃ B : X →L[ℝ] X →L[ℝ] X, ∀ u v,
      (∀ ψ, inner ℝ (B u v) ψ = fracBilinForm α τ u v ψ) ∧
        ‖B u v‖ ≤ K * τ ^ (-(3 / (4 * α))) * ‖u‖ * ‖v‖ := fun τ hτ =>
    exists_bilin_of_form (fracBilinForm α τ) (K * τ ^ (-(3 / (4 * α)))) (by positivity)
      (form_add_left h1 hτ) (form_smul_left α τ)
      (fun u v v' ψ => by
        rw [form_symm, form_add_left h1 hτ, form_symm α τ v, form_symm α τ v'])
      (fun c u v ψ => by rw [form_symm, form_smul_left, form_symm])
      (form_add_right h1 hτ) (form_smul_right α τ) (hK τ hτ)
  refine ⟨fun τ hτ => ?_, K, hK0, fun τ hτ u v => ?_⟩
  · obtain ⟨B, hB⟩ := hB τ hτ
    exact ⟨B, fun u v ψ => (hB u v).1 ψ⟩
  · obtain ⟨B, hB⟩ := hB τ hτ
    have h : 0 < τ ∧ ∃ B, FracBilinSpec α τ B := ⟨hτ, B, fun u v ψ => (hB u v).1 ψ⟩
    have hspec : FracBilinSpec α τ (fracBilinX α τ) := by
      unfold fracBilinX
      rw [dif_pos h]
      exact h.2.choose_spec
    have heq : fracBilinX α τ u v = B u v := ext_inner_right ℝ fun ψ => by
      rw [hspec, (hB u v).1]
    rw [heq]
    exact (hB u v).2

end Breakdown.Freq
