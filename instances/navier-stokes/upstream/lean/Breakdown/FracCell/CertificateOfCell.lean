import Breakdown.FracCell.Assembly
import Breakdown.FracCell.ChosenAgree
import Breakdown.FracCell.ClassAverageRows
import Breakdown.FracCell.CrossIdentity
import Breakdown.FracCell.SecondIdentity
import Breakdown.FracCell.SmoothingLower
import Breakdown.FracCell.ModelRegular
import Breakdown.FracCell.ModelLower
import Breakdown.FracCell.ModelPin
import Breakdown.FracCell.ModelField
import Breakdown.FracCell.ModelForm
import Breakdown.FracCell.CentrePairing
import Breakdown.FracCell.SplitRows
import Breakdown.FracCert.DriftEnergy
import Breakdown.FracCert.Main

open scoped ContDiff ENNReal
open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

theorem modelRegular_holds : ModelRegularStatement := modelRegular_of chosenAgree

theorem modelLower_holds : ModelLowerStatement := modelLower_of chosenAgree classAverageRows modelRegular_holds

theorem modelField_holds : ModelFieldStatement := modelField_of chosenAgree crossIdentity secondIdentity

theorem modelPin_holds : ModelPinStatement := modelPin_of chosenAgree

theorem splitRows_holds : SplitRowsStatement :=
  splitRows_of smoothingLower ChainInternal.secondSymbolEnergy_holds ChainInternal.weakPowerSymbol_holds

theorem modelForm_of_pairing (hcp : CentrePairingStatement) : ModelFormStatement :=
  modelForm_of chosenAgree secondIdentity driftEnergy hcp

theorem isFracCert_of_cell_of_pairing (hcp : CentrePairingStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (h : IsFracCell α c) : IsFracCert α (c.toCertData α) :=
  isFracCert_of_clauses modelRegular_holds modelLower_holds (modelForm_of_pairing hcp) modelField_holds modelPin_holds
    splitRows_holds α hα₁ hα₂ c h

theorem isFracCert_of_cell_of_centre (hci : CentreIdentityStatement) (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    {k N : ℕ} (c : FracCellData k N) (h : IsFracCell α c) : IsFracCert α (c.toCertData α) :=
  isFracCert_of_cell_of_pairing (centrePairing_of hci) α hα₁ hα₂ c h

theorem isFracCert_of_cell (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4) {k N : ℕ} (c : FracCellData k N)
    (h : IsFracCell α c) : IsFracCert α (c.toCertData α) :=
  isFracCert_of_cell_of_pairing centrePairing α hα₁ hα₂ c h

theorem fracCertificateHypothesis_of_cell (α : ℝ) (hα₁ : 1 < α) (hα₂ : α < 5 / 4)
    (h : FracCellCertificateHypothesis α) : FracCertificateHypothesis α := by
  obtain ⟨k, N, c, hc⟩ := h
  exact ⟨k, N, c.toCertData α, isFracCert_of_cell α hα₁ hα₂ c hc⟩

end CellCert

end Breakdown
