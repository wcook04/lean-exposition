import Breakdown.FracCert.StMildProfile
import Breakdown.Frac.RExports
import Breakdown.Frac.PAxial
import Breakdown.FreqTr.Rotation
import Breakdown.FreqTr.FieldOp

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

namespace FracInternal.SimCompose

open Breakdown.Freq.Internal.Rotation

theorem rotC_comp (R S T : Space ≃ₗᵢ[ℝ] Space) (hT : ∀ y, T y = R (S y)) (z : CSpace) :
    rotC T z = rotC R (rotC S z) := by
  ext i
  simp only [rotC_apply, hT, Finset.mul_sum]
  have hk : ∀ j : Fin 3, ((R (S (unitVector j)) i : ℝ) : ℂ) * z j =
      ∑ k : Fin 3, ((R (unitVector k) i : ℝ) : ℂ) * (((S (unitVector j) k : ℝ) : ℂ) * z j) := by
    intro j
    rw [apply_eq_sum R (S (unitVector j)) i]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [hk]
  rw [Finset.sum_comm]

theorem rotX_comp (R S T : Space ≃ₗᵢ[ℝ] Space) (hT : ∀ y, T y = R (S y)) (x : X) :
    rotX R (rotX S x) = rotX T x := by
  apply Subtype.ext
  rw [rotX_coe fieldOpRealized, rotX_coe fieldOpRealized, rotX_coe fieldOpRealized]
  have hsymm : ∀ ξ, T.symm ξ = S.symm (R.symm ξ) := by
    intro ξ
    apply T.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hT, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [rotL2_realized fieldOpRealized R (rotL2 S (x : L2C)),
    ae_comp (qmp_liso R.symm) (rotL2_realized fieldOpRealized S (x : L2C)),
    rotL2_realized fieldOpRealized T (x : L2C)] with ξ a b c
  rw [a, b, c, hsymm, rotC_comp R S T hT]

theorem rotX_refl (x : X) : rotX (LinearIsometryEquiv.refl ℝ Space) x = x := by
  have h := rotX_comp (LinearIsometryEquiv.refl ℝ Space) (LinearIsometryEquiv.refl ℝ Space)
    (LinearIsometryEquiv.refl ℝ Space) (fun _ => rfl)
  have hinj := (rotX (LinearIsometryEquiv.refl ℝ Space)).injective
  exact hinj (h x)

end FracInternal.SimCompose

open FracInternal.SimCompose in
theorem simOpCompose : SimOpComposeStatement := by
  intro α a hα
  have hD := fracDilationAlgebra_holds α hα
  have hRot := fracRotationAlgebra α (by linarith) (fracHeatSemigroup α) hD
  have hspec := axialRotationSpec
  refine ⟨fun x => ?_, fun μ ν hμ hν x => ?_⟩
  · have hsim : simOp α a 1 x = fracDilX α 1⁻¹ (rotX (axialRotation (a * Real.log 1)) x) := rfl
    rw [hsim, Real.log_one, mul_zero, hspec.2.1, rotX_refl, inv_one, hD.2.1]
    rfl
  · have e1 : simOp α a μ (simOp α a ν x) = fracDilX α μ⁻¹ (rotX (axialRotation (a * Real.log μ))
        (fracDilX α ν⁻¹ (rotX (axialRotation (a * Real.log ν)) x))) := rfl
    have e2 : simOp α a (μ * ν) x =
        fracDilX α (μ * ν)⁻¹ (rotX (axialRotation (a * Real.log (μ * ν))) x) := rfl
    have hc : rotX (axialRotation (a * Real.log μ)) (rotX (axialRotation (a * Real.log ν)) x) =
        rotX (axialRotation (a * Real.log (μ * ν))) x :=
      rotX_comp _ _ _ (fun y => by rw [Real.log_mul hμ.ne' hν.ne', mul_add, hspec.2.2.1]) x
    have hd : fracDilX α (μ * ν)⁻¹ = (fracDilX α μ⁻¹).comp (fracDilX α ν⁻¹) := by
      rw [mul_inv]
      exact hD.2.2.1 _ _ (inv_pos.2 hμ) (inv_pos.2 hν)
    have hr : rotX (axialRotation (a * Real.log μ)) (fracDilX α ν⁻¹ (rotX (axialRotation (a * Real.log ν)) x)) =
        fracDilX α ν⁻¹ (rotX (axialRotation (a * Real.log μ)) (rotX (axialRotation (a * Real.log ν)) x)) :=
      (hRot (axialRotation (a * Real.log μ))).2 ν⁻¹ _
    have hd' : fracDilX α μ⁻¹ (fracDilX α ν⁻¹ (rotX (axialRotation (a * Real.log (μ * ν))) x)) =
        fracDilX α (μ * ν)⁻¹ (rotX (axialRotation (a * Real.log (μ * ν))) x) := by
      rw [hd]
      rfl
    exact e1.trans ((congrArg (fracDilX α μ⁻¹) hr).trans
      ((congrArg (fun w => fracDilX α μ⁻¹ (fracDilX α ν⁻¹ w)) hc).trans (hd'.trans e2.symm)))

end Breakdown.FracCert
