import Breakdown.FracCert.Defs

namespace Breakdown.SteadyCert

open MeasureTheory

def QuadraticSquareIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H → MemLp (fun y => G y (v y)) 2 volume

end Breakdown.SteadyCert
