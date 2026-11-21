import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

def HarmonicCornerDataStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (L : CellLayout), IsHarmonicLayout m K B L.modes L →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
      IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg → ∀ ν : ℤ,
        (∀ (n : L.modes), Even ((n : ℤ) + ν) → ∀ (c : Fin L.cornerCount) (a : Fin 3),
          harmonicData L ν v G H Pg (CellDatum.cornerVelocity n c a)
            = cornerMoment (L.corner c).1 (L.cornerOther c).1 (L.corner c).2 (L.cornerOther c).2
                (fun p => velAt m (harmonicMode ν n) v a p) (gradAt m (harmonicMode ν n) G a 0)
                (gradAt m (harmonicMode ν n) G a 2) (slopeAt m (harmonicMode ν n) H a 0 2)) ∧
        (Even ν → ∀ c : Fin L.cornerCount,
          harmonicData L ν v G H Pg (CellDatum.cornerStream c)
            = heightStripMoment (L.corner c).2 (L.cornerOther c).2 0 (L.corner c).1 (fun r => r)
                (fun p => velAt m (harmonicMode ν 0) v 2 p) (gradAt m (harmonicMode ν 0) G 2 2) (fun _ => 1))

def OddStreamZeroStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (L : CellLayout), IsHarmonicLayout m K B L.modes L →
    ∀ (Γ : Set Symmetry) (P : ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (Pg : ℝ → Space → Space),
      IsPerturbation Γ P v G H g → Bridge.IsModeClass Γ m → ∀ ν : ℤ, Odd ν → ∀ c : Fin L.cornerCount,
        harmonicData L ν v G H Pg (CellDatum.cornerStream c) = 0

def ChosenPressureFlipHolds : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM), PressureFacts D →
    ∀ q ∈ D.cert.params, ∀ x : AdmissibleTuple D D.coercivity q,
      ∀ᵐ z : ℝ × Space, chosenPressure D x z.1 (flipPoint z.2) = flipPoint (chosenPressure D x z.1 z.2)

end Assembly

end CertCell

end Breakdown
