import Breakdown.CellReduction.AdjointEntryDefs
import Breakdown.CertCell.ShapeJetEntry
import Breakdown.CertCell.ShapeSupport
import Breakdown.CertCell.StatementDefs

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape AdjointDefect
open CellCert.GivenFields (weightPoly heightRatio radialVec polarVecQ cellCount)

def ThetaPotentialRegular : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F → ∃ C : ℝ,
    ContDiff ℝ 1 (fun z : ℝ × Space => vectorPotential P F PotKeyData.theta z.1 z.2) ∧
    (∀ σ, ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (vectorPotential P F PotKeyData.theta σ) y (unitVector j))
      (fun y => (secondDeriv (vectorPotential P F PotKeyData.theta σ) y).flip (unitVector j))) ∧
    (∀ σ y, ‖vectorPotential P F PotKeyData.theta σ y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
      ‖fderiv ℝ (vectorPotential P F PotKeyData.theta σ) y‖ ≤ C / (1 + ‖y‖) ^ 3) ∧
    ∀ σ, ∀ᵐ y, ‖secondDerivTrace (secondDeriv (vectorPotential P F PotKeyData.theta σ) y)‖ ≤ C / (1 + ‖y‖) ^ 4

def PhiPotentialRegular : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F → ∃ C : ℝ,
    ContDiff ℝ 1 (fun z : ℝ × Space => vectorPotential P F PotKeyData.phi z.1 z.2) ∧
    (∀ σ, ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (vectorPotential P F PotKeyData.phi σ) y (unitVector j))
      (fun y => (secondDeriv (vectorPotential P F PotKeyData.phi σ) y).flip (unitVector j))) ∧
    (∀ σ y, ‖vectorPotential P F PotKeyData.phi σ y‖ ≤ C / (1 + ‖y‖) ∧
      ‖fderiv ℝ (vectorPotential P F PotKeyData.phi σ) y‖ ≤ C / (1 + ‖y‖) ^ 2) ∧
    ∀ σ, ∀ᵐ y, ‖secondDerivTrace (secondDeriv (vectorPotential P F PotKeyData.phi σ) y)‖ ≤ C / (1 + ‖y‖) ^ 3

def FluxPotentialRegular : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F → ∃ C : ℝ,
    AEStronglyMeasurable (fun z : ℝ × Space => fluxMap P F z.1 z.2) volume ∧
    (∀ σ, IsWeakMatrixDivergence (fluxMap P F σ) (matrixDivergence (fluxMap P F σ))) ∧
    (∀ σ y, ‖fluxMap P F σ y‖ ≤ C / (1 + ‖y‖) ^ 2) ∧
    ∀ σ, ∀ᵐ y, ‖y‖ * ‖matrixDivergence (fluxMap P F σ) y‖ ≤ C / (1 + ‖y‖) ^ 2

def PressurePotentialRegular : Prop :=
  ∀ (P : ShapeParams) (F : PotentialSeries), IsShapeParams P → IsPotentialSeries F → ∃ C : ℝ,
    AEStronglyMeasurable (fun z : ℝ × Space => pressureValue P F z.1 z.2) volume ∧
    (∀ σ, IsWeakScalarGradient (pressureValue P F σ) (gradientAt (pressureValue P F σ))) ∧
    (∀ σ y, |pressureValue P F σ y| ≤ C / (1 + ‖y‖) ^ 2) ∧
    ∀ σ, ∀ᵐ y, ‖y‖ * ‖gradientAt (pressureValue P F σ) y‖ ≤ C ∧ ‖y‖ ^ 3 * ‖gradientAt (pressureValue P F σ) y‖ ≤ C

def CellPotentialRegular : Prop :=
  ∀ (m : ℕ) (G : CylModeData) (Rmesh Rsupp : ℝ), IsCylModeData Rmesh Rsupp G →
    AEStronglyMeasurable (fun z : ℝ × Space => cylField m G z.1 z.2) volume ∧
    AEStronglyMeasurable (fun z : ℝ × Space => fderiv ℝ (cylField m G z.1) z.2) volume ∧
    (∀ σ, IsWeakGradient (cylField m G σ) (fun y => fderiv ℝ (cylField m G σ) y)) ∧
    periodLIntegral (fun σ y => matSq (fderiv ℝ (cylField m G σ) y)) < ⊤ ∧
    ∀ σ y, 2 * Rsupp ≤ ‖y‖ → cylField m G σ y = 0

def CompactFieldSecondRegular : Prop :=
  ∀ (P : ShapeParams) (D : TimeFieldData) (tb : ℝ), IsShapeParams P → IsCompactTimeFieldData tb D →
    (∀ σ, ∀ j : Fin 3, IsWeakGradient (fun y => fderiv ℝ (shapeInfoField P D σ) y (unitVector j))
      (fun y => (secondDeriv (shapeInfoField P D σ) y).flip (unitVector j))) ∧
    (∀ σ, ∀ᵐ y, DifferentiableAt ℝ (fun x => fderiv ℝ (shapeInfoField P D σ) x) y) ∧
    ∃ C : ℝ, ∀ σ, ∀ᵐ y, ‖secondDeriv (shapeInfoField P D σ) y‖ ≤ C

structure PotentialPieces : Prop where
  theta : ThetaPotentialRegular
  phi : PhiPotentialRegular
  flux : FluxPotentialRegular
  pressure : PressurePotentialRegular
  cell : CellPotentialRegular
  generator : CompactFieldSecondRegular
  field_smooth : FieldJointSmooth
  support : CompactFieldSupportRadius
  pin_cells : Instance.CellMatFieldRegular

theorem potentialData_mono {p : PotentialData} {C C' : ℝ} (h : IsPotentialData p C) (hC : C ≤ C') :
    IsPotentialData p C' := by
  refine
    { theta_smooth := h.theta_smooth
      phi_smooth := h.phi_smooth
      flux_measurable := h.flux_measurable
      pressure_measurable := h.pressure_measurable
      theta_weak := h.theta_weak
      phi_weak := h.phi_weak
      flux_weak := h.flux_weak
      pressure_weak := h.pressure_weak
      value_decay := fun σ y => ?_
      second_decay := fun σ => ?_ }
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.value_decay σ y
    exact ⟨h1.trans (by gcongr), h2.trans (by gcongr), h3.trans (by gcongr), h4.trans (by gcongr),
      h5.trans (by gcongr), h6.trans (by gcongr)⟩
  · filter_upwards [h.second_decay σ] with y hy
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy
    exact ⟨h1.trans (by gcongr), h2.trans (by gcongr), h3.trans (by gcongr), h4.trans hC, h5.trans hC⟩

theorem potentialData_of_series (h : PotentialPieces) (P : ShapeParams) (F : PotentialSeries) (hP : IsShapeParams P)
    (hF : IsPotentialSeries F) : ∃ C, IsPotentialData (F.toPotentialData P) C := by
  obtain ⟨C1, hs1, hw1, hd1, ha1⟩ := h.theta P F hP hF
  obtain ⟨C2, hs2, hw2, hd2, ha2⟩ := h.phi P F hP hF
  obtain ⟨C3, hm3, hw3, hd3, ha3⟩ := h.flux P F hP hF
  obtain ⟨C4, hm4, hw4, hd4, ha4⟩ := h.pressure P F hP hF
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  have e1 : C1 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_left _ _) (le_max_left _ _)
  have e2 : C2 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_right _ _) (le_max_left _ _)
  have e3 : C3 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_left _ _) (le_max_right _ _)
  have e4 : C4 ≤ max (max C1 C2) (max C3 C4) := le_trans (le_max_right _ _) (le_max_right _ _)
  refine
    { theta_smooth := hs1
      phi_smooth := hs2
      flux_measurable := hm3
      pressure_measurable := hm4
      theta_weak := hw1
      phi_weak := hw2
      flux_weak := hw3
      pressure_weak := hw4
      value_decay := fun σ y => ⟨(hd1 σ y).1.trans (by gcongr), (hd1 σ y).2.trans (by gcongr),
        (hd2 σ y).1.trans (by gcongr), (hd2 σ y).2.trans (by gcongr), (hd3 σ y).trans (by gcongr),
        (hd4 σ y).trans (by gcongr)⟩
      second_decay := fun σ => ?_ }
  filter_upwards [ha1 σ, ha2 σ, ha3 σ, ha4 σ] with y h1 h2 h3 h4
  exact ⟨h1.trans (by gcongr), h2.trans (by gcongr), h3.trans (by gcongr), h4.1.trans e4, h4.2.trans e4⟩

theorem pinData_of_entry (h : PotentialPieces) {k : ℕ} (R : PinShapeEntry k) (hR : IsPinShapeEntry R) :
    ∃ C R₀, IsPinData R.pinField R.pinData C R₀ := by
  have hg : ∀ l, ∃ C : ℝ, ∀ σ, ∀ᵐ y, ‖secondDeriv (shapeInfoField (R.params l) (R.generators l) σ) y‖ ≤ C :=
    fun l => (h.generator (R.params l) (R.generators l) (R.edge l) (hR.params_valid l) (hR.generators_valid l)).2.2
  choose Cg hCg using hg
  set rad : Fin k → ℝ := fun l => (R.params l).chartLength * R.edge l / (1 - R.edge l)
  refine ⟨∑ l, |Cg l|, 2 * |R.cellSupport| + ∑ l, |rad l| + 1, ?_⟩
  have hRs : R.cellSupport ≤ |R.cellSupport| := le_abs_self _
  have hsum : ∀ l, |rad l| ≤ ∑ l, |rad l| := fun l =>
    Finset.single_le_sum (f := fun l => |rad l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
  have hsumC : ∀ l, |Cg l| ≤ ∑ l, |Cg l| := fun l =>
    Finset.single_le_sum (f := fun l => |Cg l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)
  have hsum0 : 0 ≤ ∑ l, |rad l| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  exact
    { pin_measurable := fun l => (h.pin_cells R.mesh (R.pinCells l) R.azimuthOrder hR.mesh_valid).1
      potential_measurable := fun l =>
        (h.cell R.azimuthOrder (R.cells l) R.cellMesh R.cellSupport (hR.cells_valid l)).1
      potentialGrad_measurable := fun l =>
        (h.cell R.azimuthOrder (R.cells l) R.cellMesh R.cellSupport (hR.cells_valid l)).2.1
      potential_weak := fun l =>
        (h.cell R.azimuthOrder (R.cells l) R.cellMesh R.cellSupport (hR.cells_valid l)).2.2.1
      potentialGrad_finite := fun l =>
        (h.cell R.azimuthOrder (R.cells l) R.cellMesh R.cellSupport (hR.cells_valid l)).2.2.2.1
      potential_support := fun l σ y hy =>
        (h.cell R.azimuthOrder (R.cells l) R.cellMesh R.cellSupport (hR.cells_valid l)).2.2.2.2 σ y
          (by linarith)
      generator_smooth := fun l =>
        (h.field_smooth (R.params l) (R.generators l) (hR.params_valid l) (hR.generators_valid l).field).1
      generator_periodic := fun l =>
        (h.field_smooth (R.params l) (R.generators l) (hR.params_valid l) (hR.generators_valid l).field).2.1
      generator_differentiable := fun l =>
        (h.generator (R.params l) (R.generators l) (R.edge l) (hR.params_valid l) (hR.generators_valid l)).2.1
      generator_weak := fun l =>
        (h.generator (R.params l) (R.generators l) (R.edge l) (hR.params_valid l) (hR.generators_valid l)).1
      generator_support := fun l σ y hy =>
        h.support (R.params l) (R.generators l) (R.edge l) (hR.params_valid l) (hR.generators_valid l)
          (hR.generators_break l) σ y (by
            have h1 := le_abs_self (rad l)
            have h2 := hsum l
            have h3 := abs_nonneg R.cellSupport
            show rad l < ‖y‖
            linarith)
      generatorSecond_bound := fun l σ => (hCg l σ).mono fun y hy => hy.trans ((le_abs_self _).trans (hsumC l)) }

end PotentialShape

end Breakdown
