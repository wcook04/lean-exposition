import Breakdown.CertCell.RowProfileDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

private theorem sumSq_nonneg_leaf (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq s := by
  unfold sumSq
  positivity

private theorem curlSq_nonneg_leaf (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ curlSq s := by
  unfold curlSq
  positivity

private theorem vecSq_nonneg_leaf (v : Fin 3 → ℂ) : 0 ≤ vecSq v := by
  unfold vecSq
  positivity

theorem leafDensityLower_holds : LeafDensityLowerStatement := by
  intro K _ resolved coef ch T hT ι hι p hp x2 xc s v
  have hm := hT.matrix_le ι hι p hp s v
  have hh := hT.hessFloor_le ι hι p hp
  have hc := hT.curlHessFloor_le ι hι p hp
  have h1 : Real.sqrt (sumSq s) ^ 2 = sumSq s := Real.sq_sqrt (sumSq_nonneg_leaf s)
  have h2 : Real.sqrt (curlSq s) ^ 2 = curlSq s := Real.sq_sqrt (curlSq_nonneg_leaf s)
  have h3 : Real.sqrt (vecSq v) ^ 2 = vecSq v := Real.sq_sqrt (vecSq_nonneg_leaf v)
  have hx2 : T.hessFloor ι * x2 ^ 2 ≤ (coef ι p).hess * x2 ^ 2 :=
    mul_le_mul_of_nonneg_right hh (sq_nonneg x2)
  have hxc : T.curlHessFloor ι * xc ^ 2 ≤ (coef ι p).curlHess * xc ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg xc)
  unfold ModeCoefficients.value
  rw [h1, h2, h3]
  unfold coefPairValue at hm
  linarith

end CellCalculus

end CertCell

end Breakdown
