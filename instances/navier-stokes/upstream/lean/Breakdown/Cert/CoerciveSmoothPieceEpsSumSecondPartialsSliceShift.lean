import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveModeRotation

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.ModeSlice

private theorem rot_lintegral (φ : ℝ) {f : Space → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f (axialRot φ y) = ∫⁻ y, f y := by
  have hR := (ModeDerivative.Internal.rotIso axialRotationHolds_proof φ).measurePreserving
  have e : (fun y => f (axialRot φ y))
      = fun y => f (ModeDerivative.Internal.rotIso axialRotationHolds_proof φ y) := by
    funext y
    rw [ModeDerivative.Internal.rotIso_apply]
  rw [e]
  exact hR.lintegral_comp hf

private theorem periodic_shift_Ioc {Φ : ℝ → ℝ≥0∞} (hΦ : Function.Periodic Φ 1) (σ : ℝ) :
    ∫⁻ τ in Set.Ioc (0 : ℝ) 1, Φ (σ + τ) = ∫⁻ τ in Set.Icc (0 : ℝ) 1, Φ τ := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have h1 : ∀ τ : ℝ, Φ (σ + τ) = hΦ.lift ((τ : AddCircle (1 : ℝ)) + (σ : AddCircle (1 : ℝ))) := by
    intro τ
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe, add_comm]
  have h2 : ∀ τ : ℝ, Φ τ = hΦ.lift (τ : AddCircle (1 : ℝ)) := fun τ => (Function.Periodic.lift_coe hΦ τ).symm
  simp_rw [h1]
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  simp_rw [h2]
  have a1 := AddCircle.lintegral_preimage 1 0 (fun x => hΦ.lift (x + (σ : AddCircle (1 : ℝ))))
  have a2 := AddCircle.lintegral_preimage 1 0 (fun x => hΦ.lift x)
  rw [zero_add] at a1 a2
  rw [a1, a2, lintegral_add_right_eq_self (fun x => hΦ.lift x) (σ : AddCircle (1 : ℝ))]

theorem lintegral_box_rot_shift (g : ℝ → Space → ℝ) (hg : Continuous (fun z : ℝ × Space => g z.1 z.2))
    (hgp : IsTimePeriodic g) (σ : ℝ) :
    ∫⁻ y, ∫⁻ p, ENNReal.ofReal (g (σ + p.1) (axialRot p.2 y) ^ 2) ∂Internal.ModeRotation.boxMeasure
      = ENNReal.ofReal (2 * Real.pi) * periodLIntegral (fun s x => g s x ^ 2) := by
  have hr : Continuous (fun q : Space × ℝ × ℝ => axialRot q.2.2 q.1) := by
    unfold axialRot
    fun_prop
  have hc : Continuous (fun q : Space × ℝ × ℝ => ENNReal.ofReal (g (σ + q.2.1) (axialRot q.2.2 q.1) ^ 2)) :=
    ENNReal.continuous_ofReal.comp ((hg.comp ((continuous_const.add continuous_snd.fst).prodMk hr)).pow 2)
  rw [lintegral_lintegral_swap hc.measurable.aemeasurable]
  have hg2 : Measurable (fun z : ℝ × Space => ENNReal.ofReal (g z.1 z.2 ^ 2)) :=
    (ENNReal.continuous_ofReal.comp (hg.pow 2)).measurable
  have e1 : ∀ p : ℝ × ℝ, ∫⁻ y, ENNReal.ofReal (g (σ + p.1) (axialRot p.2 y) ^ 2)
      = ∫⁻ y, ENNReal.ofReal (g (σ + p.1) y ^ 2) := fun p =>
    rot_lintegral p.2 (f := fun y => ENNReal.ofReal (g (σ + p.1) y ^ 2))
      (hg2.comp (measurable_const.prodMk measurable_id))
  simp_rw [e1]
  set Φ : ℝ → ℝ≥0∞ := fun s => ∫⁻ y, ENNReal.ofReal (g s y ^ 2) with hΦdef
  have hΦm : Measurable Φ := hg2.lintegral_prod_right'
  have hΦp : Function.Periodic Φ 1 := fun s => by
    simp only [hΦdef]
    refine lintegral_congr fun y => ?_
    rw [hgp s y]
  show ∫⁻ p, Φ (σ + p.1) ∂Internal.ModeRotation.boxMeasure = _
  rw [Internal.ModeRotation.boxMeasure,
    lintegral_prod (fun p : ℝ × ℝ => Φ (σ + p.1))
      ((hΦm.comp (measurable_const.add measurable_fst) : Measurable fun p : ℝ × ℝ => Φ (σ + p.1)).aemeasurable)]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  rw [lintegral_mul_const' (ENNReal.ofReal (2 * Real.pi)) (fun τ : ℝ => Φ (σ + τ)) ENNReal.ofReal_ne_top,
    periodic_shift_Ioc hΦp σ, mul_comm]
  rfl

end Internal.ModeSlice

end Coercive

end Breakdown
