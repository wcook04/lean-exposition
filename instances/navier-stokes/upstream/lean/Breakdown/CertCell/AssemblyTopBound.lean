import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.AssemblyTopBoundCore

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCert CellCert.CellAnalysis CellCert.CellFormula CellCalculus

theorem topBound_of (hV : Bridge.VelocitySixthIntegralHolds) : TopBoundHolds := by
  intro k C nE nM D R A _ _ states hCC hstates htop K q v G H g κ F Pg ht ζ η ι hι
  have hP : IsPeriodicSecondOrder v G H :=
    periodicSecondOrder_of_perturbation hV Bridge.secondDerivEnergyIdentity _ _ v G H g ht.perturbation
  obtain ⟨c0, S0, hord, hres, hLc⟩ := (hCC.layouts_valid K).layout_valid ι hι
  have hK : IsCellBox (D.mesh.box K) := hLc.box_valid
  have hB : IsCellBases (D.mesh.box K) (R.layouts K).bases := hLc.bases_valid
  have hQ : 2 ≤ ((R.layouts K).layout ι).degCoef := by
    have := hLc.degSide_pos
    have := hLc.degSide_le
    omega
  have hmodes : ((R.layouts K).layout ι).modes = {ι.1} := hLc.modes_eq.trans hres
  have hordL : ((R.layouts K).layout ι).order = D.azimuthOrder := hLc.order_eq.trans hord
  have hKL : IsCellBox ((R.layouts K).layout ι).box := by
    rw [hLc.box_eq]
    exact hK
  have hdata : ∀ (n : ((R.layouts K).layout ι).modes) (a b : Fin 3) (j l : Fin (((R.layouts K).layout ι).degCoef + 1)),
      restrictData D R K ⟨ι, hι⟩ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (CellDatum.lowStrain n a b j l)
        = (R.layouts K).bases.coef (D.mesh.box K) (fun p => gradAt D.azimuthOrder ι G a b p) j l := by
    intro n a b j l
    have h := TopBound.Internal.label_lowStrain_data hP Pg ι ((R.layouts K).layout ι) hKL hordL hmodes n a b j l
    rw [hLc.box_eq, hLc.bases_eq] at h
    exact h
  have hone : ∀ f : ℝ, (∑ _n : ((R.layouts K).layout ι).modes, f) = f := by
    intro f
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hmodes, Finset.card_singleton, one_smul]
  have htop1 := htop K ⟨ι, hι⟩ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) (hstates K q v G H g κ F Pg ht ζ η)
  dsimp only at htop1
  rw [htop1]
  simp only [topValue, tailVelSq, tailStrainSq, TailBand.velTailGain, hdata, hone]
  exact TopBound.Internal.label_tail_bound hP ι hK hB hQ

end Breakdown.CertCell.Assembly
