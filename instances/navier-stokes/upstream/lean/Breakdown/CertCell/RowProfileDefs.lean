import Breakdown.CertCell.CellCalculusStatements

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

def radialStripTrace (c o : ℝ) (F dF : ℝ × ℝ → ℂ) (z : ℝ) : ℂ :=
  edgeSign c o * ∫ r in Set.Icc (min c o) (max c o),
    ((((1 / (c - o) : ℝ)) : ℂ) * F (r, z) + (((r - o) / (c - o) : ℝ) : ℂ) * dF (r, z))

def heightStripTrace (c o : ℝ) (F dF : ℝ × ℝ → ℂ) (r : ℝ) : ℂ :=
  edgeSign c o * ∫ z in Set.Icc (min c o) (max c o),
    ((((1 / (c - o) : ℝ)) : ℂ) * F (r, z) + (((z - o) / (c - o) : ℝ) : ℂ) * dF (r, z))

def otherRadius (K : CellBox) (e : Fin 2) : ℝ := if e = 0 then K.r₂ else K.r₁

def otherHeight (K : CellBox) (e : Fin 2) : ℝ := if e = 0 then K.z₂ else K.z₁

def labelPressure (m : ℕ) (ι : ℤ × ℤ) (Pg : ℝ → Space → Space) (p : ℝ × ℝ) : ℂ :=
  presMode m ι.1 (potentialOf (harmonicCos (labelTime ι) Pg)) p.1 p.2
    + Complex.I * presMode m ι.1 (potentialOf (harmonicSin (labelTime ι) Pg)) p.1 p.2

def labelRowProfile (K : CellBox) (m : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) : RowProfile where
  vel := velArray m ι v
  grad := gradArray m ι G
  lap := fun p a => ∑ c : Fin 3, slopeAt m ι H a c c p
  presGrad := velArray m ι Pg
  radialSide := fun e z a => radialStripTrace (sideRadius K e) (otherRadius K e) (gradAt m ι G a 0)
    (slopeAt m ι H a 0 0) z
  heightSide := fun e r a => heightStripTrace (sideHeight K e) (otherHeight K e) (gradAt m ι G a 2)
    (slopeAt m ι H a 2 2) r
  radialPres := fun e z => radialStripTrace (sideRadius K e) (otherRadius K e) (labelPressure m ι Pg)
    (fun p => velAt m ι Pg 0 p) z
  heightPres := fun e r => heightStripTrace (sideHeight K e) (otherHeight K e) (labelPressure m ι Pg)
    (fun p => velAt m ι Pg 2 p) r

end CellCalculus

end CertCell

end Breakdown
