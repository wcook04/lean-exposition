import Breakdown.FracCell.MeshDefs
import Breakdown.FracCell.ReductionPointwiseDefs
import Breakdown.FracCell.StatementDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

def FarFloorStatement : Prop :=
  ∀ (α : ℝ) {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (W : WeightData)
    (F : FarMajorantData),
    IsCellBox K → IsWeightForm c K S W → IsWeightTests α c K S W → S.degHigh + 1 ≤ S.degNear →
    IsFarFloorTests c K S W F →
      ∀ n j l, S.degNear < max j l →
        (n ∈ S.resolved ∪ S.band → F.strainFloor ≤ S.symWeight n j l ∧ F.strainFloor ≤ S.antiWeight n j l) ∧
        (n ∈ S.resolved → F.velocityFloor ≤ S.velWeight n j l)

def TurnBoundStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (S : CellScalars) (W : WeightData) (F : FarMajorantData),
    3 ≤ c.order →
    S.band = Finset.Icc (-((W.J + W.JB : ℕ) : ℤ)) ((W.J + W.JB : ℕ) : ℤ) \ Finset.Icc (-(W.J : ℤ)) W.J →
    1 / ((((W.J + 1 : ℕ) : ℝ) * c.order) - 1) ≤ F.turnBound →
      ∀ n ∈ S.band, ∀ w : Fin 3 → ℂ,
        vecSq (turnAdjInv (azimuth c.order n) w) ≤ F.turnBound ^ 2 * vecSq w

def TailColumnBoundStatement : Prop :=
  ∀ (K : CellBox) (B : CellBases), IsCellBox K → IsCellBases K B → ∀ (D : ℕ)
    {I O : Type} [Fintype I] [Fintype O] (T : TailFamily I O), IsTailRegular K T →
      IsTailColumnBound K B D T → IsTailBounds K B D T

end Reduction

end CellCert

end Breakdown
