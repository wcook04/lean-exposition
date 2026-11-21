import Breakdown.FracCell.StEnergyProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

private lemma quadFormValue_add_sub_add {D : Type} [Fintype D] (A B C : Matrix D D ℂ) (u : D → ℂ) :
    quadFormValue (A - B + C) u = quadFormValue A u - quadFormValue B u + quadFormValue C u := by
  unfold quadFormValue
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub, Complex.add_re, Complex.sub_re]

theorem localFormBound_of (hE : EnergyFormStatement) (hC : ClassFormStatement) (hP : PairFormStatement)
    (hX : CrossFormStatement) : LocalFormBoundStatement := by
  intro α D _ _ k N c K B S Cl modes Q q I hm hQ hq hK hB hS hD hCl v G H hF u hR κ ζ
  have hset : EnergySetting α c K B S I v G H u :=
    ⟨hm, hQ, hq, hK, hB, hS, hF, hR, hD⟩
  rw [hX α c K B S Cl I v G H u hset κ ζ, quadFormValue_add_sub_add, hE α c K B S I v G H u hset,
    hC α c K B S Cl I v G H u hset hCl, hP α c K B S I v G H u hset]
  unfold CellScalars.localCellForm
  exact le_refl _

end Breakdown.CellCert.CellEnergy
