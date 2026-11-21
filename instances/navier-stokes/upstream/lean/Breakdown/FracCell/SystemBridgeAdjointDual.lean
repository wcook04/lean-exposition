import Breakdown.FracCell.CellSystemDefs
import Breakdown.FracCell.GivenAuxDual
import Breakdown.FracCell.GivenAuxAdjoint
import Breakdown.FracCell.GivenAuxPin
import Breakdown.FracCell.GivenProfileBounds
import Breakdown.FracCell.GivenAuxShift
import Breakdown.FracCell.GivenAuxInverseSquare

open scoped ContDiff ENNReal
open MeasureTheory Matrix Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

namespace Internal

theorem sharpTraceOf_spec {k : ℕ} (P : ChartParams) (A : AuxData k) (ν : ℝ) (j : Fin k) (p : Fin k → ℝ)
    (hex : ∃ L : Space → Space, IsWeakNegTraceOf (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) L ∧
      MemLp (fun y => ‖y‖ • L y) 2 volume) :
    IsWeakNegTraceOf (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) (sharpTraceOf P A ν j p) ∧
      MemLp (fun y => ‖y‖ • sharpTraceOf P A ν j p y) 2 volume := by
  unfold sharpTraceOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem pinSecondTraceOf_spec {k : ℕ} (P : ChartParams) (A : AuxData k) (l : Fin k)
    (hex : ∃ q : (Space → (Space →L[ℝ] Space →L[ℝ] Space)) × (Space → Space),
      AEStronglyMeasurable q.1 volume ∧ IsWeakSecondDerivOf (fun y => fderiv ℝ (A.pinPotentialField P l) y) q.1 ∧
      (∃ C : ℝ, ∀ᵐ y ∂volume, ‖q.1 y‖ ≤ C) ∧
      IsWeakNegTraceOf (A.pinPotentialField P l) q.2 ∧ AEStronglyMeasurable q.2 volume ∧
      (∃ C : ℝ, ∀ᵐ y ∂volume, ‖q.2 y‖ ≤ C)) :
    AEStronglyMeasurable (pinSecondTraceOf P A l).1 volume ∧
      IsWeakSecondDerivOf (fun y => fderiv ℝ (A.pinPotentialField P l) y) (pinSecondTraceOf P A l).1 ∧
      (∃ C : ℝ, ∀ᵐ y ∂volume, ‖(pinSecondTraceOf P A l).1 y‖ ≤ C) ∧
      IsWeakNegTraceOf (A.pinPotentialField P l) (pinSecondTraceOf P A l).2 ∧
      AEStronglyMeasurable (pinSecondTraceOf P A l).2 volume ∧
      (∃ C : ℝ, ∀ᵐ y ∂volume, ‖(pinSecondTraceOf P A l).2 y‖ ≤ C) := by
  unfold pinSecondTraceOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem dualTraceOf_spec {k : ℕ} (P : ChartParams) (A : AuxData k) (j : Fin k) (p : Fin k → ℝ)
    (hex : ∃ L : Space → Space, IsWeakNegTraceOf (A.dualFieldOf P j p) L ∧ MemLp (fun y => ‖y‖ • L y) 2 volume) :
    IsWeakNegTraceOf (A.dualFieldOf P j p) (dualTraceOf P A j p) ∧
      MemLp (fun y => ‖y‖ • dualTraceOf P A j p y) 2 volume := by
  unfold dualTraceOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem potentialTraceOf_spec {k : ℕ} (P : ChartParams) (A : AuxData k) (j : Fin k) (p : Fin k → ℝ)
    (hex : ∃ L : Space → Space, IsWeakNegTraceOf (A.potentialFieldOf P j p) L ∧ MemLp (fun y => ‖y‖ • L y) 2 volume) :
    IsWeakNegTraceOf (A.potentialFieldOf P j p) (potentialTraceOf P A j p) ∧
      MemLp (fun y => ‖y‖ • potentialTraceOf P A j p y) 2 volume := by
  unfold potentialTraceOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem fluxDivOf_spec {k : ℕ} (P : ChartParams) (A : AuxData k) (j : Fin k) (p : Fin k → ℝ)
    (hex : ∃ Dv : Space → Space, IsWeakMatrixDivergenceOf (A.fluxFieldOf P j p) Dv ∧
      MemLp (fun y => ‖y‖ • Dv y) 2 volume) :
    IsWeakMatrixDivergenceOf (A.fluxFieldOf P j p) (fluxDivOf P A j p) ∧
      MemLp (fun y => ‖y‖ • fluxDivOf P A j p y) 2 volume := by
  unfold fluxDivOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem inverseSquareChoice_spec (α : ℝ) {k N : ℕ} (D : ProfileData k) (d : FracCertData k N) (j : Fin k)
    (p : Fin k → ℝ) (Dd : AdjointDual k)
    (hex : ∃ q : (Space → Space) × Finset ℤ, (∀ᵐ y ∂volume, q.1 y = inverseSquarePartOf α D d j p Dd y) ∧
      AEStronglyMeasurable q.1 volume ∧ MemLp (fun y => ‖y‖ • q.1 y) 2 volume ∧
      ∀ n ∉ q.2, ∀ ρ z : ℝ, angularMode (horizontalPart q.1) n ρ z = 0 ∧ angularMode (verticalPart q.1) n ρ z = 0) :
    (∀ᵐ y ∂volume, (inverseSquareChoice α D d j p Dd).1 y = inverseSquarePartOf α D d j p Dd y) ∧
      AEStronglyMeasurable (inverseSquareChoice α D d j p Dd).1 volume ∧
      MemLp (fun y => ‖y‖ • (inverseSquareChoice α D d j p Dd).1 y) 2 volume ∧
      ∀ n ∉ (inverseSquareChoice α D d j p Dd).2, ∀ ρ z : ℝ,
        angularMode (horizontalPart (inverseSquareChoice α D d j p Dd).1) n ρ z = 0 ∧
          angularMode (verticalPart (inverseSquareChoice α D d j p Dd).1) n ρ z = 0 := by
  unfold inverseSquareChoice
  rw [dif_pos hex]
  exact hex.choose_spec

end Internal

theorem adjointDualStructure_of {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N)
    (h : IsGivenData c D A M MD RD) (hpow : D.power = 501 / 500) (hamp : ∀ i, Pi.single i 1 ∈ D.index)
    (nums : AdjointNumbers k) (j : Fin k) (p : Fin k → ℝ) :
    IsAdjointDualStructure (501 / 500) c.toFracCertData j p
      (adjointDualOf (501 / 500) D c.toFracCertData A c.splitVisc j p nums) := by
  have hD := h.profile
  have hA := h.aux
  have hI := h.aux_instance
  have hd := h.profile_instance
  have hP := hD.chart
  have hadjE : c.adjoint j p = A.adjointField D.chart j p := hI.adjoint_eq j p
  have hshE : c.adjointSharp j p = A.sharpField D.chart c.splitVisc j p := hI.adjointSharp_eq j p
  obtain ⟨hg, hm, hex, hsh2, hshg, hshm, hshi⟩ := adjointDualCore_of_given D.chart hP A hA c.splitVisc j p
  have hsharp := Internal.sharpTraceOf_spec D.chart A c.splitVisc j p hex
  have hreg := adjointRegular_of_given D.chart hP A hA j p
  have hpinR := fun l => pinRegular_of_given D.chart hP A hA l
  have hpinS : ∀ l, _ := fun l => Internal.pinSecondTraceOf_spec D.chart A l (by
    obtain ⟨-, -, H, L, h1, h2, h3, h4, h5, h6⟩ := hpinR l
    exact ⟨(H, L), h1, h2, h3, h4, h5, h6⟩)
  have hpress := adjointPressure_of_given D.chart hP A hA j p
  obtain ⟨⟨L1, hL1, hD2, hL1w, hDg, hDm, hDi⟩, ⟨L2, hTg, hL2, hT2, hTm, hTi, hL2w⟩, ⟨Dv, hDv, hFm, hFi, hDvw⟩⟩ :=
    dualFields_of_given D.chart hP A hA j p
  have hdualS := Internal.dualTraceOf_spec D.chart A j p ⟨L1, hL1, hL1w⟩
  have hpotS := Internal.potentialTraceOf_spec D.chart A j p ⟨L2, hL2, hL2w⟩
  have hfluxS := Internal.fluxDivOf_spec D.chart A j p ⟨Dv, hDv, hDvw⟩
  have hsharpC : IsWeakNegTraceOf (fun y => c.splitVisc • c.adjoint j p y + c.adjointSharp j p y)
      (sharpTraceOf D.chart A c.splitVisc j p) := by
    rw [hadjE, hshE]
    exact hsharp.1
  have hα : (501 / 500 : ℝ) = D.power := hpow.symm
  have hex2 := inverseSquare_of_given (501 / 500) D hD A hA c hd hI hα hamp j p
    (adjointDualCore D A c.splitVisc j p nums) rfl (fun l => ⟨rfl, rfl⟩) rfl rfl rfl rfl hsharpC
    (fun l => (hpinS l).2.2.2.1) hpress.2.1 hdualS.1 hpotS.1 hfluxS.1 hsharp.2
    (fun l => ⟨(hpinS l).2.2.2.2.1, (hpinS l).2.2.2.2.2⟩) ⟨hpress.1, hpress.2.2.1⟩ hdualS.2 hpotS.2
    ⟨hFm, hFi, hfluxS.2⟩
  have hchoice := Internal.inverseSquareChoice_spec (501 / 500) D c.toFracCertData j p
    (adjointDualCore D A c.splitVisc j p nums) (by
      obtain ⟨part, hae, hm', hw, S, hS⟩ := hex2
      exact ⟨(part, S), hae, hm', hw, hS⟩)
  refine
    { adjoint_gradient := ?_
      adjoint_measurable := ?_
      adjoint_regular := ?_
      sharp_trace := hsharpC
      sharp_weighted := ?_
      pin_regular := ?_
      pin_field := ?_
      pressure_gradient := hpress.2.1
      pressure_two := ⟨hpress.1, hpress.2.2.1⟩
      dual_trace := hdualS.1
      dual_two := ⟨hD2, hdualS.2, hDg, hDm, hDi⟩
      potential_gradient := hTg
      potential_trace := hpotS.1
      potential_two := ⟨hT2, hTm, hTi, hpotS.2⟩
      flux_divergence := hfluxS.1
      flux_two := ⟨hFm, hFi, hfluxS.2⟩
      remainder_split := ?_
      shift_regular := ?_
      inverseSquare_part := ⟨hchoice.2.1, hchoice.2.2.1⟩
      inverseSquare_modes := hchoice.2.2.2
      shift_weighted := ?_ }
  · rw [hadjE]; exact hg
  · rw [hadjE]; exact hm
  · rw [hadjE]; exact hreg
  · rw [hshE]; exact ⟨hsharp.2, hsh2, hshg, hshm, hshi⟩
  · intro l
    exact ⟨(hpinR l).1, (hpinR l).2.1, (hpinS l).1, (hpinS l).2.1, (hpinS l).2.2.1, (hpinS l).2.2.2.1,
      (hpinS l).2.2.2.2.1, (hpinS l).2.2.2.2.2⟩
  · exact pinField_of D A c hI
  · filter_upwards [hchoice.1] with y hy
    change _ = (inverseSquareChoice (501 / 500) D c.toFracCertData j p
      (adjointDualCore D A c.splitVisc j p nums)).1 y + _
    rw [hy]
    unfold inverseSquarePartOf
    exact (sub_add_cancel _ _).symm
  · intro i
    obtain ⟨h1, h2, C, hC⟩ := amplitude_regular_of D hD i p (hamp i)
    exact ⟨h1, fun y => rfl, h2, C, hC⟩
  · intro i
    rw [hadjE]
    obtain ⟨hU, -, C, hb⟩ := amplitude_regular_of D hD i p (hamp i)
    exact FracInternal.weighted_pair_integrable (amplitudeFieldAt D i p) hU C hb _
      (adjointRegular_of_given D.chart hD.chart A hA j p).1

end CellSystem

end CellCert

end Breakdown
