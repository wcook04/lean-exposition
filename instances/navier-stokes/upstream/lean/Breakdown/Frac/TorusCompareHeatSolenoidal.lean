import Breakdown.Frac.StTorusStepCompare
import Breakdown.Frac.RExports
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracShiftCompare.Internal

open Breakdown.Freq

theorem phiSmul_norm_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (ξ : Space) :
    ‖fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace‖ ≤ τ ^ (-(1 / (2 * α))) := by
  refine (norm_smul_le _ _).trans ?_
  have h1 := Breakdown.FracInternal.PhiBound.fracPhiFactor_le hα hτ ξ
  rw [Real.norm_eq_abs]
  calc |fracPhiFactor α τ ξ| * ‖ContinuousLinearMap.id ℝ CSpace‖
      ≤ τ ^ (-(1 / (2 * α))) * 1 :=
        mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) (Real.rpow_nonneg hτ.le _)
    _ = τ ^ (-(1 / (2 * α))) := mul_one _

theorem phiSmul_aesm (α τ : ℝ) :
    AEStronglyMeasurable (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
      volume := by
  have hm : Measurable (fun ξ : Space => fracPhiFactor α τ ξ) := by
    unfold fracPhiFactor; fun_prop
  exact hm.aestronglyMeasurable.smul aestronglyMeasurable_const

theorem phiOp_ae {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (f : L2C) :
    (fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) f : Space → CSpace)
      =ᵐ[volume] fun ξ => fracPhiFactor α τ ξ • (f : Space → CSpace) ξ := by
  have h := fieldOpRealized_holds (ContinuousLinearEquiv.refl ℝ Space) _ _ (phiSmul_aesm α τ)
    (phiSmul_norm_le hα hτ) f
  simpa using h

theorem heat_mul_phi (α : ℝ) {t τ : ℝ} (ht : 0 ≤ t) (ξ : Space) :
    fracPhiFactor α τ ξ * fracHeatFactor α t ξ = fracPhiFactor α (t + τ) ξ := by
  unfold fracPhiFactor fracHeatFactor
  rw [max_eq_left ht, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem phiOp_heat {α t τ : ℝ} (hα : 1 < α) (ht : 0 ≤ t) (hτ : 0 < τ) (f : L2C) :
    fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace) (fracHeatL2 α t f) =
      fieldOp id (fun ξ => fracPhiFactor α (t + τ) ξ • ContinuousLinearMap.id ℝ CSpace) f := by
  have htτ : 0 < t + τ := by linarith
  apply Lp.ext
  filter_upwards [phiOp_ae hα hτ (fracHeatL2 α t f), phiOp_ae hα htτ f,
    Breakdown.FracInternal.RHeat.op_ae α t f] with ξ h1 h2 h3
  rw [h1, h2, h3, smul_smul, heat_mul_phi α ht]

theorem phiX_heat {α t τ : ℝ} (hα : 1 < α) (hH : FracHeatSemigroup α) (ht : 0 ≤ t) (hτ : 0 < τ)
    (ψ : X) : fracPhiX α τ (fracHeatX α t ψ) = fracPhiX α (t + τ) ψ := by
  unfold fracPhiX
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [hH.2.2.2.2.2 t ψ, phiOp_heat hα ht hτ]

theorem inner_complexifyVec (a : Space) (b : CSpace) :
    inner ℝ (complexifyVec a) b = inner ℝ a (realVec b) := by
  simp [complexifyVec, realVec, PiLp.inner_apply, Complex.inner]

theorem inner_complexify (g : L2R) (z : L2C) :
    inner ℝ (Freq.complexify g) z = inner ℝ g (Freq.realPart z) := by
  have hx : (Freq.complexify g : Space → CSpace) =ᵐ[volume] fun a => complexifyVec (g a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hy : (Freq.realPart z : Space → Space) =ᵐ[volume] fun a => realVec (z a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hx, hy] with x hx hy
  rw [hx, hy, inner_complexifyVec]

def transformIsometry : L2C ≃ₗᵢ[ℝ] L2C :=
  { freqTrL2.toLinearEquiv.restrictScalars ℝ with norm_map' := freqTrL2.norm_map }

theorem inner_transform (a b : L2C) :
    inner ℝ (freqTrR a) b = inner ℝ a (freqTrInvR b) :=
  transformIsometry.inner_map_eq_flip a b

theorem proj_inner {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (g : L2R) (ψ : X) :
    inner ℝ (fracHeatSolenoidal α τ g) ψ = inner ℝ g (fracPhiX α τ ψ) := by
  set M := fieldOp id (fun ξ => fracPhiFactor α τ ξ • ContinuousLinearMap.id ℝ CSpace)
    with hMdef
  have hsa : ∀ a b : L2C, inner ℝ (M a) b = inner ℝ a (M b) := by
    intro a b
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [phiOp_ae hα hτ a, phiOp_ae hα hτ b] with x ha hb
    rw [ha, hb, real_inner_smul_left, real_inner_smul_right]
  have hproj : ∀ w : L2C, inner ℝ (projX w) ψ = inner ℝ w (ψ : L2C) := fun w =>
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right ψ w
  show inner ℝ (projX (M (freqTrR (Freq.complexify g)))) ψ = inner ℝ g (Freq.realPart (freqTrInvR (M ψ)))
  rw [hproj, hsa, inner_transform, inner_complexify]

end FracShiftCompare.Internal

open FracShiftCompare.Internal

theorem fracHeatSolenoidalShift (α : ℝ) (hα : 1 < α) (hH : Freq.FracHeatSemigroup α) :
    FracHeatSolenoidalShift α := by
  intro t τ ht hτ A
  have htτ : 0 < t + τ := by linarith
  apply ext_inner_right ℝ
  intro ψ
  rw [hH.2.2.2.2.1, proj_inner hα hτ, proj_inner hα htτ, phiX_heat hα hH ht hτ]

end Breakdown.Periodic
