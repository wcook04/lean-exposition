import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.BridgeStatements

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem periodicSecondOrder_of_perturbation (h4 : Bridge.VelocitySixthIntegralHolds)
    (h5 : Bridge.HessianEnergyIdentityHolds) (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) : IsPeriodicSecondOrder v G H where
  measurable_velocity := hv.measurable_velocity
  measurable_gradient := hv.measurable_gradient
  measurable_secondDeriv := hv.measurable_secondDeriv
  periodic_velocity := hv.periodic_velocity
  periodic_gradient := hv.periodic_gradient
  periodic_secondDeriv := hv.periodic_secondDeriv
  weak_gradient := hv.weak_gradient
  weak_secondDeriv := hv.weak_secondDeriv
  divergence_free := hv.divergence_free
  sixth_power_integrated := h4 Γ P v G H g hv
  gradient_finite := hv.gradient_finite
  hessian_finite := by
    show periodLIntegral (fun σ y => Bridge.hessFrobSq (H σ y)) < ⊤
    rw [h5 Γ P v G H g hv]
    exact hv.sumSecondPartials_finite

end CellCalculus

end CertCell

end Breakdown
