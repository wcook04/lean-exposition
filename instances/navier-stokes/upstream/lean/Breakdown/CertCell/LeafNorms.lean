import Breakdown.CertCell.RowProfileDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal

theorem permSign_eq_alternatingSymbol (i j l : Fin 3) :
    permSign i j l = alternatingSymbol i j l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [permSign, alternatingSymbol]

end Internal

theorem leafNorms_holds : LeafNormsStatement := by
  intro m ι v G H p _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [cnormSq, vecSq, velArray, velAt]
  · simp only [cnormSq, sumSq, gradArray, gradAt, Fintype.sum_prod_type]
  · simp only [cnormSq, curlSq, curlOfGrad, curlComp, gradArray, gradAt,
      Internal.permSign_eq_alternatingSymbol]
  · simp only [cnormSq, slopeSq, slopeAt, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  · simp only [cnormSq, curlSlopeSq, curlGradOfSecondDeriv, curlComp, slopeAt, Fintype.sum_prod_type,
      Internal.permSign_eq_alternatingSymbol]

end CellCalculus

end CertCell

end Breakdown
