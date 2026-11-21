import Mathlib
import Breakdown.FracCell.StatementDefs

open Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

namespace ParamData

variable {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D)

end ParamData

def ParamRecoverStatement : Prop :=
  ∀ {D : Type} [Fintype D] [DecidableEq D] (P : ParamData D), IsParamData P →
    ∀ u : D → ℂ, P.relation *ᵥ u = 0 → P.param u = u

end Breakdown.CellCert.CellFormula
