import Breakdown.Frac.StTorusShell
import Breakdown.Torus.ShellTorus
import Breakdown.Torus.Transplant
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.CoefCalculus

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusShellTorus.Internal

theorem fracSourceOp_apply {α μ τ : ℝ} (hE : FracSourceOpExists α) (hμ : 0 < μ) (A : Freq.L2R) :
    fracSourceOp α μ τ A =
      fracTorusForce α (μ * τ) (fun x => (A : Space → Space) (simCoord (simScale α μ) x)) := by
  unfold fracSourceOp
  rw [dif_pos (hE μ τ), (hE μ τ).choose_spec A, fracSourceFun, if_pos hμ]

theorem scale_identity {α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ) :
    2 * μ ^ (3 / (4 * α)) * (-(1 / 2) * (simScale α μ)⁻¹) = -μ ^ (-(1 / (4 * α))) := by
  unfold simScale
  rw [← Real.rpow_neg hμ.le]
  have h : μ ^ (3 / (4 * α)) * μ ^ (-(1 / α)) = μ ^ (-(1 / (4 * α))) := by
    rw [← Real.rpow_add hμ]
    congr 1
    field_simp
    ring
  calc 2 * μ ^ (3 / (4 * α)) * (-(1 / 2) * μ ^ (-(1 / α)))
      = -(μ ^ (3 / (4 * α)) * μ ^ (-(1 / α))) := by ring
    _ = -μ ^ (-(1 / (4 * α))) := by rw [h]

end TorusShellTorus.Internal

open ShellTorus.Internal TorusShellTorus.Internal

theorem fracTorusFactor (α : ℝ) (hα : 1 < α) (hK : FracTorusKernelAlgebra α)
    (hF : FracTorusForceAlgebra α) (hE : FracSourceOpExists α) : FracTorusFactor α := by
  intro φ hφ b μ hμ _hμ1 hsh hsupp τ hτ z
  have hα0 : 0 < α := lt_trans one_pos hα
  have hs : 0 < μ * τ := mul_pos hμ hτ
  have hFS : FreqTrSeriesSpec := freqTrSeriesSpec coefDeriv
  apply coeff_injective
  intro k
  rw [fracLambdaTorus, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, coeff_neg_vec, coeff_smul_real, coeff_smul_real,
    fracSourceOp_apply hE hμ, hF.1, fracTorusForceCoef, if_pos hs, hK.1, fracTorusKernelCoef, if_pos hs,
    advCoef_transplant transplantSmooth hFS φ hφ b (simScale α μ) hsh hsupp z k,
    divFree_smul_real, smul_smul, smul_smul, ← neg_smul, smul_smul]
  congr 1
  rw [← scale_identity hα0 hμ]
  ring

end Breakdown.Periodic
