import Breakdown.Torus.CompareStatements
import Breakdown.FreqTr.BilinTestFormula
import Breakdown.FreqTr.Heat

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CompareHeatDivFree.Internal

open Breakdown.Freq

theorem phiFactor_smul_norm_le {τ : ℝ} (hτ : 0 < τ) (ξ : Space) :
    ‖Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace‖ ≤ 1 + 1 / τ := by
  refine (norm_smul_le _ _).trans ?_
  have hp : 0 ≤ Freq.phiFactor τ ξ := by unfold Freq.phiFactor; positivity
  refine (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_
  rw [mul_one, Real.norm_eq_abs, abs_of_nonneg hp]
  unfold Freq.phiFactor
  set y := 2 * π * ‖ξ‖ with hy
  have hy0 : 0 ≤ y := by positivity
  have harg : 4 * π ^ 2 * τ * ‖ξ‖ ^ 2 = τ * y ^ 2 := by rw [hy]; ring
  rw [harg, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have he := Real.add_one_le_exp (τ * y ^ 2)
  have hinv : 0 < 1 / τ := by positivity
  have h1 : (1 + 1 / τ) * (τ * y ^ 2 + 1) = τ * y ^ 2 + 1 + y ^ 2 + 1 / τ := by
    field_simp
    ring
  have h2 : y ≤ (1 + 1 / τ) * (τ * y ^ 2 + 1) := by
    rw [h1]
    have : 0 ≤ τ * y ^ 2 := by positivity
    nlinarith [sq_nonneg (y - 1)]
  exact h2.trans (mul_le_mul_of_nonneg_left he (by positivity))

theorem phiOp_ae (hF : Freq.FieldOpRealized) {τ : ℝ} (hτ : 0 < τ) (f : Freq.L2C) :
    (Freq.fieldOp id (fun ξ => Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) f : Space → Freq.CSpace)
      =ᵐ[volume] fun ξ => Freq.phiFactor τ ξ • (f : Space → Freq.CSpace) ξ := by
  have hc : Continuous (fun ξ : Space => Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) := by
    unfold Freq.phiFactor; fun_prop
  have := Freq.Internal.BilinTestFormula.fieldOp_id_ae hF _ (1 + 1 / τ) hc.aestronglyMeasurable
    (phiFactor_smul_norm_le hτ) f
  simpa using this

theorem heatFactor_mul_phiFactor {t τ : ℝ} (ht : 0 ≤ t) (ξ : Space) :
    Freq.phiFactor τ ξ * Freq.heatFactor t ξ = Freq.phiFactor (t + τ) ξ := by
  unfold Freq.phiFactor Freq.heatFactor
  rw [max_eq_left ht, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem phiOp_heat (hF : Freq.FieldOpRealized) {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ) (f : Freq.L2C) :
    Freq.fieldOp id (fun ξ => Freq.phiFactor τ ξ • ContinuousLinearMap.id ℝ Freq.CSpace) (Freq.heatL2 t f) =
      Freq.fieldOp id (fun ξ => Freq.phiFactor (t + τ) ξ • ContinuousLinearMap.id ℝ Freq.CSpace) f := by
  have htτ : 0 < t + τ := by linarith
  apply Lp.ext
  filter_upwards [phiOp_ae hF hτ (Freq.heatL2 t f), phiOp_ae hF htτ f,
    Freq.Internal.Heat.heat_ae hF t f] with ξ h1 h2 h3
  rw [h1, h2, h3, smul_smul, heatFactor_mul_phiFactor ht]

theorem phiX_heat (hF : Freq.FieldOpRealized) (hH : Freq.HeatSemigroup) {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ)
    (ψ : Freq.X) : Freq.phiX τ (Freq.heatX t ψ) = Freq.phiX (t + τ) ψ := by
  unfold Freq.phiX
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [hH.2.2.2.2.2 t ψ, phiOp_heat hF ht hτ]

end CompareHeatDivFree.Internal

open CompareHeatDivFree.Internal

theorem heatDivFreeShift (hF : Freq.FieldOpRealized) (hH : Freq.HeatSemigroup) : HeatDivFreeShift := by
  intro t τ ht hτ A
  have htτ : 0 < t + τ := by linarith
  apply ext_inner_right ℝ
  intro ψ
  rw [hH.2.2.2.2.1, Freq.Internal.BilinTestFormula.heatDivFree_inner hF hτ,
    Freq.Internal.BilinTestFormula.heatDivFree_inner hF htτ, phiX_heat hF hH ht hτ]

theorem heatDivFreeContinuous (hS : HeatDivFreeShift) (hH : Freq.HeatSemigroup) :
    HeatDivFreeContinuous := by
  intro A
  refine fun τ₀ hτ₀ => (ContinuousAt.continuousWithinAt ?_)
  have hτ₀ : 0 < τ₀ := hτ₀
  have hh : 0 < τ₀ / 2 := by linarith
  set x := Freq.heatDivFree (τ₀ / 2) A
  have hc : ContinuousAt (fun τ => Freq.heatX (τ - τ₀ / 2) x) τ₀ := by
    have hw : ContinuousWithinAt (fun t => Freq.heatX t x) (Ici 0) (τ₀ - τ₀ / 2) :=
      hH.2.2.2.1 x _ (by simp only [mem_Ici]; linarith)
    have hat : ContinuousAt (fun t => Freq.heatX t x) (τ₀ - τ₀ / 2) :=
      hw.continuousAt (Ici_mem_nhds (by linarith))
    exact hat.comp (f := fun τ : ℝ => τ - τ₀ / 2) (by fun_prop)
  refine hc.congr ?_
  filter_upwards [lt_mem_nhds (show τ₀ / 2 < τ₀ by linarith)] with τ hτ
  have := hS (τ - τ₀ / 2) (τ₀ / 2) (by linarith) hh A
  rw [sub_add_cancel] at this
  exact this

end Breakdown.Periodic
