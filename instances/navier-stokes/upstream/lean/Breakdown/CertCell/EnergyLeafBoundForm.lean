import Breakdown.CertCell.RowProfileDefs

open MeasureTheory Matrix

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

def HarmonicEnergyFormValueStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (ι : ℤ × ℤ) (L : CellLayout), IsHarmonicLayout m K B {ι.1} L →
    (K.IsAxis → ι.1 = 0) →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
      IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg → ∀ e eω : ℝ,
        quadFormValue (energyForm K B (layoutIndex L) m (fun _ => e) (fun _ => eω) (fun _ => 0))
            (harmonicData L (labelTime ι) v G H Pg)
          = e * labelStrainEnergy K m ι L.degCoef L.degSide G H
            + eω * labelVorticityEnergy K m ι L.degCoef L.degSide G H

end CellCalculus

end CertCell

end Breakdown
