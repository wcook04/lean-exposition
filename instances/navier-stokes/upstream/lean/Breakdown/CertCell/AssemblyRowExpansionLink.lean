import Breakdown.CertCell.AssemblyRowParts

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

theorem rowMomentExpansion_of_parts (hI : RowIdentityHolds) (hF : FreqPieceBoundHolds)
    (hE : ErrorPieceBoundHolds) (hL : LongPieceBoundHolds) (hS : DeactSplitHolds) (hD : DeactPieceBoundHolds)
    (hAct : ActuatorPieceBoundHolds) (hA : AllowanceSplitHolds) (hCmb : RowCombineHolds) :
    RowMomentExpansionHolds := by
  intro k C nE nM D R A P states hreg htf tauMax hT hstates hP hC hRF
  exact hCmb D R A P states hstates hC hRF
    (hI D R A P states hstates hreg htf tauMax hT hreg.field.actuators hreg.field.mode_class hP hC hRF)
    (hF D R A P states hstates hreg htf hC hRF)
    (hE D R A P states hstates hreg htf hP.velocity_off_labels hP.vorticity_off_labels hC hRF)
    (hL D R A P states hstates hreg htf hC hRF)
    (hS D R A P states hstates hreg htf hP hC hRF)
    (hD D R A P states hstates hreg htf hP hC hRF)
    (hAct D R A P states hstates hreg htf hC hRF)
    (hA D R A P states hstates hreg htf hRF.cell_conditions hP hC hRF)

end Assembly

end CertCell

end Breakdown
