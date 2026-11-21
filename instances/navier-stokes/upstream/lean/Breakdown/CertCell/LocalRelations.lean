import Breakdown.CertCell.LocalFieldDefs
import Breakdown.CertCell.LocalModeWeak
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.CertCell.LocalRelationsA
import Breakdown.CertCell.LocalRelationsTurnSide
import Breakdown.CertCell.LocalRelationsB
import Breakdown.FracCell.ParamRecover

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

theorem localRelationsHold_of (h1 : LocalRelRadialCoefStatement) (h2 : LocalRelHeightCoefStatement)
    (h3 : LocalRelTurnStatement) (h4 : LocalRelTraceStatement) (h5 : LocalRelZeroModeStatement)
    (h6 : LocalRelRadialSideStatement) (h7 : LocalRelHeightSideStatement) (h8 : LocalRelAxisStatement)
    (h9 : LocalRelStreamStatement) (h10 : LocalRelSideSplitStatement) : LocalRelationsHoldStatement := by
  intro k N c K S B L hL x hx ρ
  rcases ρ with ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ | ρ
  · exact h1 c K S B L hL x hx ρ
  · exact h2 c K S B L hL x hx ρ
  · exact h3 c K S B L hL x hx ρ
  · exact h4 c K S B L hL x hx ρ
  · exact h5 c K S B L hL x hx ρ
  · exact h6 c K S B L hL x hx ρ
  · exact h7 c K S B L hL x hx ρ
  · exact h8 c K S B L hL x hx ρ
  · exact h9 c K S B L hL x hx ρ
  · exact h10 c K S B L hL x hx ρ

theorem localTrueParam_of (h : LocalRelationsHoldStatement) : LocalTrueParamStatement := by
  intro k N c K S B L hL P sel hP x hx
  refine paramRecover P hP.param (L.trueData x) ?_
  funext i
  rw [Pi.zero_apply, Matrix.mulVec, dotProduct, hP.rows i]
  exact h c K S B L hL x hx (sel i)

theorem localStripTrace : LocalStripTraceStatement :=
  localStripTrace_of localModeStripIntegrable

theorem localCylinderFlux : LocalCylinderFluxStatement :=
  localCylinderFlux_of localModeStripIntegrable localAngularMode localStripTrace

theorem localAxisFlux : LocalAxisFluxStatement :=
  localAxisFlux_of localAxisModeIntegrable localAngularMode

theorem localRelationsHold : LocalRelationsHoldStatement :=
  localRelationsHold_of localRelRadialCoef (localRelHeightCoef_of localHeightModeIbp)
    (localRelTurn_of localModeIntegrable localAngularMode) localRelTrace localRelZeroMode
    (localRelRadialSide_of localModeRadialWeak) (localRelHeightSide_of localHeightModeIbp localModeIntegrable)
    (localRelAxis_of localAxisModeIntegrable localAxisFlux)
    (localRelStream_of localModeStripIntegrable localCylinderFlux)
    (localRelSideSplit_of localModeRectIntegrable)

theorem localTrueParam : LocalTrueParamStatement :=
  localTrueParam_of localRelationsHold

end Breakdown.CertCell.LocalField
